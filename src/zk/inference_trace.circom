pragma circom 2.1.8;

include "circomlib/circuits/poseidon.circom";
include "circomlib/circuits/comparators.circom";
include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/mux1.circom";

function FIXED_POINT_SCALE() {
    return 1000000;
}

function FIXED_POINT_QUADRATIC_DIVISOR() {
    return 2000000;
}

function FIXED_POINT_CUBIC_DIVISOR() {
    return 6000000000000;
}

function REMAINDER_BIT_SIZE() {
    return 20;
}

function QUADRATIC_REMAINDER_BIT_SIZE() {
    return 21;
}

function CUBIC_REMAINDER_BIT_SIZE() {
    return 43;
}

function INTERNAL_BIT_SIZE() {
    return 192;
}

function ERROR_ACCUMULATION_BIT_SIZE() {
    return 252;
}

function EXP_INPUT_MAX() {
    return 1000000;
}

template PoseidonChain(n) {
    assert(n > 0);

    signal input in[n];
    signal output out;

    var num_chunks = (n + 5) \ 6;

    signal chain[num_chunks + 1];

    component block_hashers[num_chunks];
    component chain_hashers[num_chunks];

    chain[0] <== 0;

    for (var chunk = 0; chunk < num_chunks; chunk++) {
        block_hashers[chunk] = Poseidon(6);

        for (var j = 0; j < 6; j++) {
            if (chunk * 6 + j < n) {
                block_hashers[chunk].inputs[j] <== in[chunk * 6 + j];
            } else {
                block_hashers[chunk].inputs[j] <== 0;
            }
        }

        chain_hashers[chunk] = Poseidon(2);
        chain_hashers[chunk].inputs[0] <== chain[chunk];
        chain_hashers[chunk].inputs[1] <== block_hashers[chunk].out;

        chain[chunk + 1] <== chain_hashers[chunk].out;
    }

    out <== chain[num_chunks];
}

template SafeIsZero() {
    signal input in;
    signal output out;

    signal inv;
    signal prod;

    inv <-- in != 0 ? 1 / in : 0;

    prod <== in * inv;
    out <== 1 - prod;

    in * out === 0;
    out * (out - 1) === 0;
}

template SafeIsEqual() {
    signal input a;
    signal input b;
    signal output out;

    signal diff;

    component is_zero = SafeIsZero();

    diff <== a - b;

    is_zero.in <== diff;

    out <== is_zero.out;
}

template HashCommit() {
    signal input value;
    signal input blinding;
    signal output commitment;

    component hasher = Poseidon(2);

    hasher.inputs[0] <== value;
    hasher.inputs[1] <== blinding;

    commitment <== hasher.out;
}

template RSFLayerComputation(dim, precision_bits) {
    assert(dim > 0);
    assert(dim % 2 == 0);
    assert(precision_bits > 0);
    assert(precision_bits <= 64);

    var half = dim \ 2;

    signal input x[dim];
    signal input weights_s[half][half];
    signal input weights_t[half][half];
    signal input bias_s[half];
    signal input bias_t[half];
    signal input expected_commitment;

    signal output y[dim];
    signal output valid_commitment;

    component x_range[dim];
    component weights_s_range[half][half];
    component weights_t_range[half][half];
    component bias_s_range[half];
    component bias_t_range[half];

    signal x1[half];
    signal x2[half];

    for (var i = 0; i < dim; i++) {
        x_range[i] = Num2Bits(precision_bits);
        x_range[i].in <== x[i];
    }

    for (var i = 0; i < half; i++) {
        x1[i] <== x[i];
        x2[i] <== x[half + i];

        bias_s_range[i] = Num2Bits(precision_bits);
        bias_s_range[i].in <== bias_s[i];

        bias_t_range[i] = Num2Bits(precision_bits);
        bias_t_range[i].in <== bias_t[i];

        for (var j = 0; j < half; j++) {
            weights_s_range[i][j] = Num2Bits(precision_bits);
            weights_s_range[i][j].in <== weights_s[i][j];

            weights_t_range[i][j] = Num2Bits(precision_bits);
            weights_t_range[i][j].in <== weights_t[i][j];
        }
    }

    signal s_accumulators[half][half + 1];
    signal s_products[half][half];
    signal s_pre_clip[half];

    for (var i = 0; i < half; i++) {
        s_accumulators[i][0] <== bias_s[i];

        for (var j = 0; j < half; j++) {
            s_products[i][j] <== weights_s[i][j] * x2[j];
            s_accumulators[i][j + 1] <== s_accumulators[i][j] + s_products[i][j];
        }

        s_pre_clip[i] <== s_accumulators[i][half];
    }

    component s_pre_clip_range[half];
    component s_clip_selector[half];

    signal clipped_s[half];

    for (var i = 0; i < half; i++) {
        s_pre_clip_range[i] = Num2Bits(INTERNAL_BIT_SIZE());
        s_pre_clip_range[i].in <== s_pre_clip[i];

        s_clip_selector[i] = LessThan(INTERNAL_BIT_SIZE());
        s_clip_selector[i].in[0] <== s_pre_clip[i];
        s_clip_selector[i].in[1] <== EXP_INPUT_MAX() + 1;

        clipped_s[i] <== s_clip_selector[i].out * s_pre_clip[i] + (1 - s_clip_selector[i].out) * EXP_INPUT_MAX();
    }

    signal s_square[half];
    signal s_cubic[half];

    signal quadratic_quotient[half];
    signal quadratic_remainder[half];
    signal cubic_quotient[half];
    signal cubic_remainder[half];

    component quadratic_remainder_bound[half];
    component cubic_remainder_bound[half];

    signal exp_scaled[half];

    signal x1_scaled[half];
    signal y1_quotient[half];
    signal y1_remainder[half];

    component y1_remainder_bound[half];
    component y1_range[half];

    signal y1[half];

    for (var i = 0; i < half; i++) {
        s_square[i] <== clipped_s[i] * clipped_s[i];
        s_cubic[i] <== s_square[i] * clipped_s[i];

        quadratic_quotient[i] <-- s_square[i] \ FIXED_POINT_QUADRATIC_DIVISOR();
        quadratic_remainder[i] <-- s_square[i] % FIXED_POINT_QUADRATIC_DIVISOR();

        quadratic_quotient[i] * FIXED_POINT_QUADRATIC_DIVISOR() + quadratic_remainder[i] === s_square[i];

        quadratic_remainder_bound[i] = LessThan(QUADRATIC_REMAINDER_BIT_SIZE());
        quadratic_remainder_bound[i].in[0] <== quadratic_remainder[i];
        quadratic_remainder_bound[i].in[1] <== FIXED_POINT_QUADRATIC_DIVISOR();
        quadratic_remainder_bound[i].out === 1;

        cubic_quotient[i] <-- s_cubic[i] \ FIXED_POINT_CUBIC_DIVISOR();
        cubic_remainder[i] <-- s_cubic[i] % FIXED_POINT_CUBIC_DIVISOR();

        cubic_quotient[i] * FIXED_POINT_CUBIC_DIVISOR() + cubic_remainder[i] === s_cubic[i];

        cubic_remainder_bound[i] = LessThan(CUBIC_REMAINDER_BIT_SIZE());
        cubic_remainder_bound[i].in[0] <== cubic_remainder[i];
        cubic_remainder_bound[i].in[1] <== FIXED_POINT_CUBIC_DIVISOR();
        cubic_remainder_bound[i].out === 1;

        exp_scaled[i] <== FIXED_POINT_SCALE() + clipped_s[i] + quadratic_quotient[i] + cubic_quotient[i];

        x1_scaled[i] <== x1[i] * exp_scaled[i];

        y1_quotient[i] <-- x1_scaled[i] \ FIXED_POINT_SCALE();
        y1_remainder[i] <-- x1_scaled[i] % FIXED_POINT_SCALE();

        y1_quotient[i] * FIXED_POINT_SCALE() + y1_remainder[i] === x1_scaled[i];

        y1_remainder_bound[i] = LessThan(REMAINDER_BIT_SIZE());
        y1_remainder_bound[i].in[0] <== y1_remainder[i];
        y1_remainder_bound[i].in[1] <== FIXED_POINT_SCALE();
        y1_remainder_bound[i].out === 1;

        y1_range[i] = Num2Bits(precision_bits);
        y1_range[i].in <== y1_quotient[i];

        y1[i] <== y1_quotient[i];
    }

    signal t_accumulators[half][half + 1];
    signal t_products[half][half];
    signal t_y1[half];

    for (var i = 0; i < half; i++) {
        t_accumulators[i][0] <== bias_t[i];

        for (var j = 0; j < half; j++) {
            t_products[i][j] <== weights_t[i][j] * y1[j];
            t_accumulators[i][j + 1] <== t_accumulators[i][j] + t_products[i][j];
        }

        t_y1[i] <== t_accumulators[i][half];
    }

    signal y2[half];
    component y2_range[half];

    for (var i = 0; i < half; i++) {
        y2[i] <== x2[i] + t_y1[i];

        y2_range[i] = Num2Bits(precision_bits);
        y2_range[i].in <== y2[i];
    }

    for (var i = 0; i < half; i++) {
        y[i] <== y1[i];
        y[half + i] <== y2[i];
    }

    component output_hash = PoseidonChain(dim);

    for (var i = 0; i < dim; i++) {
        output_hash.in[i] <== y[i];
    }

    component commit_check = SafeIsEqual();

    commit_check.a <== output_hash.out;
    commit_check.b <== expected_commitment;

    valid_commitment <== commit_check.out;
    valid_commitment * (valid_commitment - 1) === 0;
}

template FullInferenceProof(num_layers, dim, precision_bits) {
    assert(num_layers > 0);
    assert(dim > 0);
    assert(dim % 2 == 0);
    assert(precision_bits > 0);
    assert(precision_bits <= 64);

    var half = dim \ 2;

    signal input tokens[dim];
    signal input layer_weights_s[num_layers][half][half];
    signal input layer_weights_t[num_layers][half][half];
    signal input layer_biases_s[num_layers][half];
    signal input layer_biases_t[num_layers][half];
    signal input expected_output[dim];
    signal input input_commitment;
    signal input output_commitment;
    signal input layer_commitments[num_layers];
    signal input max_error_squared;

    signal output is_valid;

    signal layer_outputs[num_layers + 1][dim];

    component input_hash = PoseidonChain(dim);
    component input_check = SafeIsEqual();

    for (var i = 0; i < dim; i++) {
        layer_outputs[0][i] <== tokens[i];
        input_hash.in[i] <== tokens[i];
    }

    input_check.a <== input_hash.out;
    input_check.b <== input_commitment;

    component rsf_layers[num_layers];
    signal layer_valid[num_layers];

    for (var layer = 0; layer < num_layers; layer++) {
        rsf_layers[layer] = RSFLayerComputation(dim, precision_bits);

        for (var i = 0; i < dim; i++) {
            rsf_layers[layer].x[i] <== layer_outputs[layer][i];
        }

        for (var i = 0; i < half; i++) {
            rsf_layers[layer].bias_s[i] <== layer_biases_s[layer][i];
            rsf_layers[layer].bias_t[i] <== layer_biases_t[layer][i];

            for (var j = 0; j < half; j++) {
                rsf_layers[layer].weights_s[i][j] <== layer_weights_s[layer][i][j];
                rsf_layers[layer].weights_t[i][j] <== layer_weights_t[layer][i][j];
            }
        }

        rsf_layers[layer].expected_commitment <== layer_commitments[layer];

        for (var i = 0; i < dim; i++) {
            layer_outputs[layer + 1][i] <== rsf_layers[layer].y[i];
        }

        layer_valid[layer] <== rsf_layers[layer].valid_commitment;
    }

    component output_hash = PoseidonChain(dim);
    component output_check = SafeIsEqual();

    for (var i = 0; i < dim; i++) {
        output_hash.in[i] <== layer_outputs[num_layers][i];
    }

    output_check.a <== output_hash.out;
    output_check.b <== output_commitment;

    component expected_output_range[dim];

    for (var i = 0; i < dim; i++) {
        expected_output_range[i] = Num2Bits(precision_bits);
        expected_output_range[i].in <== expected_output[i];
    }

    component diff_less_than[dim];

    signal abs_diff[dim];
    signal diff_squared[dim];
    signal error_sum[dim + 1];

    error_sum[0] <== 0;

    for (var i = 0; i < dim; i++) {
        diff_less_than[i] = LessThan(precision_bits);
        diff_less_than[i].in[0] <== layer_outputs[num_layers][i];
        diff_less_than[i].in[1] <== expected_output[i];

        abs_diff[i] <== diff_less_than[i].out * (expected_output[i] - layer_outputs[num_layers][i]) + (1 - diff_less_than[i].out) * (layer_outputs[num_layers][i] - expected_output[i]);

        diff_squared[i] <== abs_diff[i] * abs_diff[i];

        error_sum[i + 1] <== error_sum[i] + diff_squared[i];
    }

    component max_error_range = Num2Bits(ERROR_ACCUMULATION_BIT_SIZE());
    component error_check = LessThan(ERROR_ACCUMULATION_BIT_SIZE());

    max_error_range.in <== max_error_squared;

    error_check.in[0] <== error_sum[dim];
    error_check.in[1] <== max_error_squared;

    signal all_layers_valid[num_layers + 1];

    all_layers_valid[0] <== 1;

    for (var layer = 0; layer < num_layers; layer++) {
        all_layers_valid[layer + 1] <== all_layers_valid[layer] * layer_valid[layer];
    }

    signal input_and_output_valid;
    signal commitment_and_error_valid;

    input_and_output_valid <== input_check.out * output_check.out;
    commitment_and_error_valid <== input_and_output_valid * error_check.out;

    is_valid <== commitment_and_error_valid * all_layers_valid[num_layers];
    is_valid * (is_valid - 1) === 0;
}

component main {public [tokens, expected_output, input_commitment, output_commitment]} = FullInferenceProof(8, 32, 64);

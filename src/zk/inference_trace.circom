pragma circom 2.1.8;

include "circomlib/circuits/poseidon.circom";
include "circomlib/circuits/comparators.circom";
include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/mux1.circom";

function FIXED_POINT_SCALE() {
    return 1000000;
}

function FIXED_POINT_SCALE_SQ() {
    return 1000000000000;
}

function TAYLOR_DENOM_QUADRATIC() {
    return 2;
}

function TAYLOR_DENOM_CUBIC() {
    return 6;
}

function REMAINDER_BIT_SIZE() {
    return 20;
}

function VALUE_BIT_SIZE() {
    return 64;
}

function COUNT_BIT_SIZE() {
    return 32;
}

function EXP_INPUT_BOUND() {
    return 5000000;
}

template PoseidonChain(n) {
    signal input in[n];
    signal output out;

    var num_chunks;
    if (n == 0) {
        num_chunks = 1;
    } else {
        num_chunks = (n + 4) \ 5;
    }

    component data_hashers[num_chunks];
    component carry_hashers[num_chunks];
    signal intermediate[num_chunks];

    for (var chunk = 0; chunk < num_chunks; chunk++) {
        var chunk_start = chunk * 5;
        var chunk_size = 5;
        if (chunk_start + chunk_size > n) {
            chunk_size = n - chunk_start;
        }
        if (chunk_size < 0) {
            chunk_size = 0;
        }

        data_hashers[chunk] = Poseidon(5);
        for (var k = 0; k < 5; k++) {
            if (k < chunk_size) {
                data_hashers[chunk].inputs[k] <== in[chunk_start + k];
            } else {
                data_hashers[chunk].inputs[k] <== 0;
            }
        }

        carry_hashers[chunk] = Poseidon(2);
        carry_hashers[chunk].inputs[0] <== data_hashers[chunk].out;
        if (chunk == 0) {
            carry_hashers[chunk].inputs[1] <== 0;
        } else {
            carry_hashers[chunk].inputs[1] <== intermediate[chunk - 1];
        }
        intermediate[chunk] <== carry_hashers[chunk].out;
    }

    out <== intermediate[num_chunks - 1];
}

template SafeIsZero() {
    signal input in;
    signal output out;

    signal inv;
    inv <-- in != 0 ? 1 / in : 0;

    signal prod;
    prod <== in * inv;

    out <== 1 - prod;

    in * out === 0;
}

template SafeIsEqual() {
    signal input a;
    signal input b;
    signal output out;

    signal diff;
    diff <== a - b;

    component isz = SafeIsZero();
    isz.in <== diff;

    out <== isz.out;
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

template SignedAbs(bits) {
    signal input in;
    signal output out;
    signal output is_negative;

    signal shifted;
    shifted <== in + (1 << bits);

    component n2b = Num2Bits(bits + 1);
    n2b.in <== shifted;

    is_negative <== 1 - n2b.out[bits];

    signal neg_in;
    neg_in <== 0 - in;

    out <== is_negative * neg_in + (1 - is_negative) * in;

    component check_pos = Num2Bits(bits);
    check_pos.in <== out;
}

template SafeLessThan(bits) {
    signal input a;
    signal input b;
    signal output out;

    component a_check = Num2Bits(bits);
    a_check.in <== a;

    component b_check = Num2Bits(bits);
    b_check.in <== b;

    component lt = LessThan(bits);
    lt.in[0] <== a;
    lt.in[1] <== b;

    out <== lt.out;
}

template RSFLayerComputation(dim) {
    signal input x[dim];
    signal input weights_s[dim \ 2][dim \ 2];
    signal input weights_t[dim \ 2][dim \ 2];
    signal input bias_s[dim \ 2];
    signal input bias_t[dim \ 2];
    signal input expected_commitment;
    signal output y[dim];
    signal output valid_commitment;

    var half = dim \ 2;

    signal x1[half];
    signal x2[half];
    for (var i = 0; i < half; i++) {
        x1[i] <== x[i];
        x2[i] <== x[half + i];
    }

    signal s_terms[half][half];
    signal s_partial[half][half + 1];
    signal s_x2_unbiased[half];
    signal s_x2[half];

    for (var i = 0; i < half; i++) {
        s_partial[i][0] <== 0;
        for (var j = 0; j < half; j++) {
            s_terms[i][j] <== weights_s[i][j] * x2[j];
            s_partial[i][j + 1] <== s_partial[i][j] + s_terms[i][j];
        }
        s_x2_unbiased[i] <== s_partial[i][half];
        s_x2[i] <== s_x2_unbiased[i] + bias_s[i];
    }

    signal s_clipped[half];
    component s_abs[half];
    component s_in_bound[half];

    for (var i = 0; i < half; i++) {
        s_abs[i] = SignedAbs(VALUE_BIT_SIZE());
        s_abs[i].in <== s_x2[i];

        s_in_bound[i] = SafeLessThan(VALUE_BIT_SIZE());
        s_in_bound[i].a <== s_abs[i].out;
        s_in_bound[i].b <== EXP_INPUT_BOUND();
        s_in_bound[i].out === 1;

        s_clipped[i] <== s_x2[i];
    }

    signal s_sq[half];
    signal s_cu[half];
    signal taylor_lin[half];
    signal taylor_quad_num[half];
    signal taylor_cub_num[half];
    signal exp_num[half];
    signal x1_scaled[half];
    signal y1[half];
    signal y1_rem[half];

    component rem_check[half];
    component rem_range[half];
    component quot_range[half];

    for (var i = 0; i < half; i++) {
        s_sq[i] <== s_clipped[i] * s_clipped[i];
        s_cu[i] <== s_sq[i] * s_clipped[i];

        taylor_lin[i] <== s_clipped[i] * FIXED_POINT_SCALE();
        taylor_quad_num[i] <== s_sq[i];
        taylor_cub_num[i] <== s_cu[i];

        exp_num[i] <== FIXED_POINT_SCALE_SQ() * TAYLOR_DENOM_CUBIC()
                    + taylor_lin[i] * TAYLOR_DENOM_CUBIC() * FIXED_POINT_SCALE() / FIXED_POINT_SCALE()
                    + taylor_quad_num[i] * TAYLOR_DENOM_CUBIC() / TAYLOR_DENOM_QUADRATIC()
                    + taylor_cub_num[i];

        x1_scaled[i] <== x1[i] * exp_num[i];

        var divisor = FIXED_POINT_SCALE_SQ() * TAYLOR_DENOM_CUBIC();

        y1[i] <-- x1_scaled[i] \ divisor;
        y1_rem[i] <-- x1_scaled[i] % divisor;

        y1[i] * divisor + y1_rem[i] === x1_scaled[i];

        rem_range[i] = Num2Bits(VALUE_BIT_SIZE());
        rem_range[i].in <== y1_rem[i];

        quot_range[i] = Num2Bits(VALUE_BIT_SIZE());
        quot_range[i].in <== y1[i] + (1 << (VALUE_BIT_SIZE() - 1));

        rem_check[i] = SafeLessThan(VALUE_BIT_SIZE());
        rem_check[i].a <== y1_rem[i];
        rem_check[i].b <== divisor;
        rem_check[i].out === 1;
    }

    signal t_terms[half][half];
    signal t_partial[half][half + 1];
    signal t_y1_unbiased[half];
    signal t_y1[half];
    signal y2[half];

    for (var i = 0; i < half; i++) {
        t_partial[i][0] <== 0;
        for (var j = 0; j < half; j++) {
            t_terms[i][j] <== weights_t[i][j] * y1[j];
            t_partial[i][j + 1] <== t_partial[i][j] + t_terms[i][j];
        }
        t_y1_unbiased[i] <== t_partial[i][half];
        t_y1[i] <== t_y1_unbiased[i] + bias_t[i];
        y2[i] <== x2[i] + t_y1[i];
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
}

template FullInferenceProof(num_layers, dim, precision_bits) {
    signal input tokens[dim];
    signal input layer_weights_s[num_layers][dim \ 2][dim \ 2];
    signal input layer_weights_t[num_layers][dim \ 2][dim \ 2];
    signal input layer_bias_s[num_layers][dim \ 2];
    signal input layer_bias_t[num_layers][dim \ 2];
    signal input expected_output[dim];
    signal input input_commitment;
    signal input output_commitment;
    signal input layer_commitments[num_layers];
    signal input max_error_squared;
    signal output is_valid;

    var half = dim \ 2;

    signal layer_outputs[num_layers + 1][dim];
    for (var i = 0; i < dim; i++) {
        layer_outputs[0][i] <== tokens[i];
    }

    component input_hash = PoseidonChain(dim);
    for (var i = 0; i < dim; i++) {
        input_hash.in[i] <== tokens[i];
    }

    component input_check = SafeIsEqual();
    input_check.a <== input_hash.out;
    input_check.b <== input_commitment;

    component rsf_layers[num_layers];
    signal layer_valid[num_layers];

    for (var layer = 0; layer < num_layers; layer++) {
        rsf_layers[layer] = RSFLayerComputation(dim);

        for (var i = 0; i < dim; i++) {
            rsf_layers[layer].x[i] <== layer_outputs[layer][i];
        }

        for (var i = 0; i < half; i++) {
            for (var j = 0; j < half; j++) {
                rsf_layers[layer].weights_s[i][j] <== layer_weights_s[layer][i][j];
                rsf_layers[layer].weights_t[i][j] <== layer_weights_t[layer][i][j];
            }
            rsf_layers[layer].bias_s[i] <== layer_bias_s[layer][i];
            rsf_layers[layer].bias_t[i] <== layer_bias_t[layer][i];
        }

        rsf_layers[layer].expected_commitment <== layer_commitments[layer];

        for (var i = 0; i < dim; i++) {
            layer_outputs[layer + 1][i] <== rsf_layers[layer].y[i];
        }

        layer_valid[layer] <== rsf_layers[layer].valid_commitment;
    }

    component output_hash = PoseidonChain(dim);
    for (var i = 0; i < dim; i++) {
        output_hash.in[i] <== layer_outputs[num_layers][i];
    }

    component output_check = SafeIsEqual();
    output_check.a <== output_hash.out;
    output_check.b <== output_commitment;

    signal diff[dim];
    signal diff_squared[dim];
    component diff_abs[dim];

    for (var i = 0; i < dim; i++) {
        diff[i] <== layer_outputs[num_layers][i] - expected_output[i];
        diff_abs[i] = SignedAbs(precision_bits \ 2);
        diff_abs[i].in <== diff[i];
        diff_squared[i] <== diff_abs[i].out * diff_abs[i].out;
    }

    signal error_sum[dim + 1];
    error_sum[0] <== 0;
    for (var i = 0; i < dim; i++) {
        error_sum[i + 1] <== error_sum[i] + diff_squared[i];
    }

    component error_range = Num2Bits(precision_bits);
    error_range.in <== error_sum[dim];

    component max_err_range = Num2Bits(precision_bits);
    max_err_range.in <== max_error_squared;

    component error_check = LessThan(precision_bits);
    error_check.in[0] <== error_sum[dim];
    error_check.in[1] <== max_error_squared;

    signal all_layers_valid[num_layers + 1];
    all_layers_valid[0] <== 1;
    for (var layer = 0; layer < num_layers; layer++) {
        all_layers_valid[layer + 1] <== all_layers_valid[layer] * layer_valid[layer];
    }

    signal v1;
    v1 <== input_check.out * output_check.out;

    signal v2;
    v2 <== v1 * error_check.out;

    signal v3;
    v3 <== v2 * all_layers_valid[num_layers];

    is_valid <== v3;
    is_valid * (is_valid - 1) === 0;
}

component main {public [tokens, expected_output, input_commitment, output_commitment]} = FullInferenceProof(8, 32, 64);

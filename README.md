Update: The formal verification of rsf.zig is complete and can be found at: src/verification/lean4/rsf.lean

## JAIDE áttekintés

A JAIDE (v40) egy kvantum-klasszikus hibrid nagy nyelvi modell, amely az alapoktól kezdve a Reversible Scatter Flow (RSF) paradigma megvalósítására épült.
A hagyományos transzformátor vagy CNN architektúrákkal ellentétben a JAIDE bijektív csatolási rétegeket használ, amelyek lehetővé teszik az O(1) memória visszaterjedést és egy paramétermentes Haar-wavelet keverő blokkot, amelyet OFTB-nek neveznek

A rendszert nagy teljesítményű futtatásra tervezték különböző hardvereken, a szabványos CPU-któl kezdve a több GPU-s B200 klasztereken át a szimulált kvantum relációs gráfokig

### Az RSF paradigma

A JAIDE lényege a Reversible Scatter Flow. Ez egy egyedülálló számítási primitívet vezet be: a kereszt-affin csatolást

- Bijektivitás: Minden előrehaladásnak van egy pontos algebrai inverze, ami biztosítja, hogy a feldolgozás során nem esik össze az információ
- Memóriahatékonyság: Mivel a hálózat reverzibilis, az aktiválásokat nem kell tárolni a backpropagációhoz. A backwardFromOutputs függvény soron belül rekonstruálja a bemeneteket a kimenetekből, így a memória komplexitása a mélységhez képest O(1) marad
- Strukturális identitás: Az RSF architektúra konzisztens 4-tenzoros struktúrát (s_weight, t_weight, s_bias, t_bias) tart fenn a Zig, a Futhark és az olyan formális verifikációs nyelvek, mint a Lean 4 és a Mizar között


### Kulcsfontosságú alrendszerek

A JAIDE több különböző, de egymással összekapcsolt alrendszerre tagolódik:

1.   Magarchitektúra: Tensor rendszer és egy sor speciális memória allokátor (Arena, Slab, Buddy)
2.   RSF feldolgozási csővezeték: Az RSFLayer az affin transzformációkhoz és az OFTB a fraktálkeveréshez
3.   Tokenizáló és visszakeresés: A morféma-vezérelt tokenizáló (MGT) és a strukturált szekvenciaindex (SSI) a hatékony tudáskereséshez és hasonlósági kereséshez.
4.   NSIR (kvantum-realizációs gráf): Egy önhasonló relációs gráf, amely a hierarchikus gondolkodáshoz a kvantumlogikát (Hadamard, CNOT kapuk) és a klasszikus aktiválást integrálja
5.   Hardveres gyorsítás: Futharkot használó multi-backend rendszer a GPU-kernelekhez (CUDA/OpenCL) és Clash-t az RTL hardver szintézishez



### Kódbázis szervezése

A tároló úgy van felépítve, hogy az alaplogika elkülönüljön a hardver-specifikus megvalósításoktól és a formális bizonyításoktól:

| Címtár | Cél |
| --- | --- |
| src/core/ | Alapvető tenzor logika és memóriakezelés. |
| src/rsf/ | Az RSFLayer, az OFTB és az SFD optimalizáló implementációja. |
| src/nsir/ | Kvantum-relációs gráf logika és érvelési rendszerezők. |
| src/hw/ | Hardveres gyorsítás (Futhark C-csomagolás és RTL). |
| src/formal/ | Formális ellenőrző bizonyítások (Lean 4, Mizar, Twelf, Bel). |
| szkriptek | | Telepítési és képzési szkriptek a Modal felhőhöz. |

### Gyermek szekciók

Részletes műszaki dokumentációért kérjük, tekintse meg a következő aloldalakat:

- Utasítások a Zig build rendszer használatához, a GPU-gyorsítás konfigurálásához és a különböző futtatható célprogramok, mint a jaide-gpu és a jaide-inference-server megértéséhez.
- Útmutató a Python-alapú infrastruktúrához (Modal), amelyet a felhőalapú képzéshez és az elosztott következtetéshez használnak.

## Kezdő lépések és rendszerépítés

### "Nyitott adattár")


### Kezdő lépések és rendszerépítés

A JAIDE a Zig build rendszer segítségével készült, amely egységes felületet biztosít a klasszikus CPU-logika, a Futhark által generált GPU-kernelek és az elosztott képzési komponensek fordításához. A build rendszer kezeli a C-ben fordított Futhark kernelek integrálását a Zig binárisba, kezeli a feltételes fordítást a GPU-gyorsításhoz, és több belépési pontot definiál a különböző telepítési forgatókönyvekhez.

### Építési manifesztum és függőségek

A projekt a szabványos Zig csomagkezelő formátumot használja. A build.zig.zon fájl határozza meg a projekt metaadatait és biztosítja a Zig fordítóval való kompatibilitást.

| Mező | Érték | Leírás |
| --- | --- | --- |
| név | .jaide | Belső csomag neve |
| verzió | 40.0.0 | Jelenlegi rendszerverzió |
| minimum_zig_version | 0.13.0 | Szükséges toolchain verzió |

### Build konfiguráció és GPU gyorsítás

Az építési folyamat középpontjában a build.zig áll. Ez egy konfigurálható zászlót biztosít a GPU-gyorsítás bekapcsolásához, ami befolyásolja, hogy mely futtatható fájlok épülnek és hogyan linkelődnek.

### GPU vs CPU módok

A JAIDE alapértelmezés szerint CPU-ra épít. A GPU-gyorsítás engedélyezéséhez a Futhark CUDA backend segítségével használja a -Dgpu=true jelzőt

Ha a gpu_acceleration engedélyezve van:

1.   A build_options modul a gpu_acceleration = true értékkel frissül
2.   További futtatható fájlok, mint a jaide-gpu és a jaide-distributed lefordításra kerülnek
3.   Minden bináris program a Futhark C forrásához kapcsolódik és tartalmazza az alábbi elérési utakat

Rendszerösszetevő áramlás építése

A következő ábra azt szemlélteti, hogy a build.zig szkript hogyan dolgozza fel a forrásfájlokat a gpu opció alapján.

### Futhark Kernel összeállítása

A JAIDE a Futharkot használja a nagy teljesítményű GPU-kernelekhez (matmul, RSF átmenetek, SSI hashing). Ezeket a kerneleket előre lefordítják C kóddá és fejlécfájlokká, amelyeket aztán a Zig építési rendszer beemel.

- Forrás File:src/hw/accel/futhark_kernels.c
- Bővített elérési út:src/hw/accel
- Optimalizálás: A C forráskódot -O2

A main_exe és más artefaktumok meghívják a linkLibC() funkciót, hogy megkönnyítsék ezt az integrációt

### Elérhető futtatható programok

A build rendszer a célkörnyezettől függően több speciális bináris programot készít:

| Végrehajtható | Forrás gyökér | Cél |
| --- | --- | --- |
| jaide | src/main.zig | CLI a képzéshez és a CPU-alapú következtetéshez |
| jaide-gpu | src/main_gpu.zig | Nagy teljesítményű GPU-gyorsított képzés |
| jaide-inference-server | src/inference_server_main.zig | HTTP/1.1 API szerver a modell kiszolgálásához |
| jaide-distributed | src/main_distributed.zig | Multi-GPU klasszikus elosztott képzés |
| jaide-distributed-futhark | src/main_distributed_futhark.zig | Multi-GPU Futhark-gyorsított képzés |

### Építési parancsok

A következő zig építési lépések a build.zig fájlban vannak definiálva:

- zig build run: Az argumentumok átadhatók a -- [args] kapcsolóval
- zig build teszt: A src/main.zig fájlban definiált egységtesztek futtatása
- zig build test-tensor: Src/core/tensor.zig-ben található tensor alrendszer tesztjeit futtatja
- zig build test-memória: Src/core/memory.zig-ben található memóriakezelő réteg tesztjeit futtatja
- zig build run-distributed: (csak GPU) Az elosztott tréner artefaktum futtatása

Adatáramlás: Építés a végrehajtásig

Ez az ábra azt mutatja, hogy a kódegységek hogyan kerülnek a végső végrehajtási környezetbe a build rendszer lépésein keresztül.


## Képzési és telepítési szkriptek

A JAIDE rendszer a Modal felhő-infrastruktúrát használja a nagy teljesítményű képzéshez és következtetéshez. Ez az infrastruktúra lehetővé teszi, hogy a rendszer több NVIDIA B200 GPU-n keresztül skálázódjon, a Futhark hardveres gyorsításhoz és az NCCL elosztott gradiens szinkronizáláshoz való felhasználásával. A képzési csővezetéket a Reversible Scatter Flow (RSF) architektúra kezelésére tervezték, biztosítva a $O(1)$ memória visszaterjedést és a hatékony paraméterfrissítést az SFD optimalizátoron keresztül.

### Környezet biztosítása

A telepítési környezetet egy többlépcsős konténer-építési folyamat határozza meg a Modal Image API segítségével. Ez a környezet konszolidálja a JAIDE hibrid architektúrájához szükséges speciális eszközláncokat.

| Komponens | Verzió / Forrás | Cél |
| --- | --- | --- |
| Base Image | nvidia/cuda:12.4.0-devel-ubuntu22.04 | CUDA futtatási idő és fejlécek |
| Zig | 0.13.0 | Elsődleges rendszerprogramozási nyelv és építési rendszer |
| Futhark | Nightly | Adatpárhuzamos GPU-kernel fordító |
| Python | 3.11 | Orchestrálás és adathalmaz-kezelés |
| Adatkészletek | HuggingFaceFW/finephrase | Alapértelmezett képzési korpusz |

A telepítési folyamatot az src/scripts/modal_setup.sh indítja el, amely hitelesíti a Modal CLI-t és inicializálja a tartós tároló köteteket: jaide-training-data és jaide-checkpoints

### Elosztott képzési architektúra

A képzést a modal_train.py és a modal_distributed_train.py programmal irányítjuk. A rendszer elosztott megközelítést alkalmaz, ahol a (src/main.zig fájlból fordított) Zig bináris program egy GPU-kból álló fürtön keresztül kerül végrehajtásra.

### Adatáramlás és végrehajtás

1.   Adatkészlet előkészítése: A _download_finephrase_to_jsonl függvény elhozza a képzési korpuszt és átalakítja azt az MGT tokenizátor számára alkalmas JSONL formátumba
2.   Kernel összeállítása: A src/hw/accel/futhark_kernels.fut állományban található Futhark kernelek C könyvtárakká fordítódnak --library móddal, hogy a Zig futtatható állományba lehessen linkelni
3.   Bináris összeállítás: A Zig build rendszer ReleaseFast optimalizálással fordítja le a jaide bináris változatát
4.   Elosztott végrehajtás: A train_jaide függvény a bináris programot a --mode train funkcióval indítja, olyan paraméterek megadásával, mint a --batch-size, --dim és --layers

### Rendszer leképezése: Természetes nyelvből kódolt entitásokba

A következő ábra a koncepcionális képzési lépéseket a végrehajtásukért felelős konkrét Python- és Zig-egységekhez kapcsolja.

A képzés végrehajtásának folyamata

### Következtetés és alkalmazás

A következtetés telepítését a modal_inference.py kezeli. Egyszeri és kötegelt következtetési képességeket is biztosít, egyetlen B200 GPU-t használva a gyorsított generáláshoz.

### Kulcsfontosságú következtetési funkciók

- következtetés: Vesz egy promptot és egy modell fájlnevet, lefuttatja a jaide bináris programot --módban infer, és visszaadja a generált szöveget a teljesítmény mérőszámokkal együtt
- batch_inference: Végigfut a felszólítások listáján, átlagos időt szolgáltat felszólításonként és egyedi állapotjelentéseket ad ki
- _runtime_build_inference: Biztosítja, hogy a következtetési bináris lefordításra és linkelésre kerüljön a helyes Futhark kernelekkel szemben a végrehajtás előtt

Következtetési kérelem csővezeték

### Konfiguráció és paraméterek

A képzési szkriptek számos CLI-argumentumot fogadnak el, amelyek közvetlenül módosítják a JAIDE modell felépítését és optimalizálását.

| Paraméter | Alapértelmezett | Leírás |
| --- | --- | --- |
| --epochs | 50 | Az adathalmazon való teljes átfutások száma |
| --batch-size | 128 | Mintavételek száma gradiens frissítésenként |
| --dim | 512 | Az RSF rétegek rejtett dimenzióssága |
| --layers | 8 | A Reversible Scatter Flow rétegek száma |
| --learning-rate | 0.0003 | Az SFD optimalizáló lépésmérete |
| --sample-limit | 100000 | A feldolgozandó adatállomány sorainak maximális száma |

### Modell perzisztencia

A modell ellenőrzési pontjait a jaide-training-data kötetben tárolja. Minden egyes ellenőrzőpont tartalmazza a modell súlyait (.bin formátumban) és egy metadata.json fájlt, amely tartalmazza a képzési veszteséget és a paramétereket A modal_train.py fájlban található list_models függvény lehetővé teszi a felhasználók számára a rendelkezésre álló ellenőrzőpontok és azok méretének lekérdezését

## Magarchitektúra

A JAIDE magarchitektúrája biztosítja az alapvető adatstruktúrákat, a speciális memóriakezelési primitíveket és a típusrendszereket, amelyek támogatják a nagy teljesítményű neurális feldolgozást és a kvantum-relációs gráfműveleteket. Ezt a réteget a hatékonyság, a szálbiztonság és a determinisztikus memóriaviselkedés érdekében tervezték.

### Építészeti áttekintés

A rendszer egy egyedi memóriakezelő rétegre épül, amely különböző allokációs stratégiákat (Arenas, Slabs, Pools) biztosít, hogy minimalizálja a töredezettséget és az overheadet a nagy teljesítményű következtetés és képzés során. A memóriaréteg tetején helyezkedik el a Tensor System, amely a többdimenziós tömbműveleteket kezeli referencia számlálással és copy-on-write (COW) szemantikával

### Rendszerentitás-leképezés: Adatok és memória

A következő ábra a magas szintű architektúrális koncepciókat a kódbázison belüli konkrét megvalósításukhoz rendeli.

Lényegkapcsolati diagram

A Tensor az elsődleges adatszerkezet minden numerikus számításhoz. Legfeljebb 8 dimenziót támogat, és egy Shape struktúrát használ a dimenziók és lépések kezelésére

A legfontosabb jellemzők:

- Referenciaszámlálás: A tenzorok nyomon követik a felhasználást a rendszerben, hogy megakadályozzák az idő előtti kiosztás megszüntetését
- Copy-on-Write (COW): A memória csak akkor duplikálódik, ha egy megosztott tenzor módosul
- SIMD gyorsítás: Az olyan műveletek, mint a mátrixszorzás és az elemenkénti transzformáció a @Vector típusokat használják a hardverszintű párhuzamosság érdekében
- TensorIterator: Tenzorok: Speciális segédprogram a nem összefüggő memória nézetek (pl. szeletelt vagy transzponált tenzorok) bejárására

A részletekért lásd

A JAIDE megkerüli a szabványos halomkiosztást a teljesítménykritikus útvonalakon, és az src/core/memory.zig fájlban definiált egyéni allokátorokat használ.

| Allokátor | Cél | Kódhivatkozás |
| --- | --- | --- |
| ArenaAllocator | Gyors, tömeges kiosztás egypontos kiosztás megszüntetéssel. | |
| SlabAllocator | Hatékony allokáció azonos méretű objektumokhoz. | |
| BuddyAllocator | Kettős elosztás a külső töredezettség minimalizálása érdekében. | |
| TrackingAllocator | Más allokátorokat csomagol be a szivárgások és a használati metrikák figyelésére. | |

A memóriaréteg olyan biztonsági primitíveket is tartalmaz, mint a secureZeroMemory az érzékeny adatok törléséhez és a ChaCha20Poly1305 a titkosított memóriarégiókhoz

A részletekért lásd

A perzisztencia réteg kezeli a modellek és tenzorok RSF0 bináris formátumba történő szerializálását. Ezt a formátumot atomi írásra (write-then-rename) tervezték, és CRC32 integritás-ellenőrzést tartalmaz az adatok konzisztenciájának biztosítása érdekében a betöltés során.

Modell perzisztencia munkafolyamat

A model_io modul magas szintű API-kat biztosít a teljes modellállapotok mentéséhez és visszaállításához, beleértve a tanult beágyazásokat és az optimalizáló paramétereket is.

A részletekért lásd

### Core típusú rendszer

A rendszer speciális numerikus típusokat definiál az src/core/types.zig állományban a különböző hardveres korlátozások és pontossági követelmények támogatása érdekében:

- Fixpontos aritmetika: FixedPoint16, FixedPoint32 és FixedPoint64 típusok lehetővé teszik a determinisztikus számítást robusztus lebegőpontos egységekkel nem rendelkező hardvereken
- Komplex számok: Complex32 és Complex64 elsősorban az NSIR alrendszerben a kvantumállapot-szimulációkhoz használatos
- Hibakezelés: Egy központi Error enum határozza meg a rendszer egészére kiterjedő hiba módokat, mint például Overflow, InvalidShape és OutOfMemory

## Tensor rendszer

A Tensor rendszer a JAIDE-n belül a többdimenziós numerikus számítások elsődleges adatszerkezete. Robusztus keretrendszert biztosít az N-dimenziós tömbök kezeléséhez, amely támogatja a komplex memóriaelrendezést, a referenciaszámlálású életciklus-kezelést és a hardveresen gyorsított lineáris algebrai műveleteket.

### Alapvető adatszerkezetek

A rendszer a Tensor struktúra és az azt támogató Shape metaadatok köré épül.

### A Tensor Struct

A Tensor struktúra f32 értékek többdimenziós tömbjét reprezentálja. Használ egy base_data mutatót az eredeti kiosztáshoz és egy adatmutatót az aktuális nézethez, lehetővé téve a nullmásolásos szeletelést és transzformációkat

| Mező | Típus | Leírás |
| --- | --- | --- |
| data | []align(32) f32 | A tenzoradatok aktív nézete. |
| base_data | []align(32) f32 | Mutató a tényleges allokáció kezdetére. |
| alakzat | Alakzat | Méreteket és lépéseket tartalmazó metaadatok. |
| allokátor | Allokátor | A tenzor memóriájához használt allokátor. |
| refcount | usize | Atomikus referenciaszámláló a memóriakezeléshez. |
| cow | bool | Jelző jelzi, hogy a tenzor Copy-On-Write állapotban van-e. |

### Alak és lépések

A Shape struktúra a tenzor geometriáját kezeli. Legfeljebb 8 dimenziót támogat Az inicializálás során automatikusan kiszámításra kerülnek a sorrendek, hogy alapértelmezés szerint megkönnyítsék a soros sorrendiséget

- Összefüggés: Egy alakzat akkor tekinthető egybefüggőnek, ha a lépései megegyeznek az egymást követő méretek szorzatával
- Műsorszolgáltatás: A broadcastCompatible függvény ellenőrzi, hogy egy tenzor kiterjeszthető-e úgy, hogy megfeleljen egy célformának az elemenkénti műveletekhez

### Kódex entitás leképezés: Tensor anatómia

Ez az ábra a Tensor magas szintű koncepcióját az src/core/tensor.zig állományban található specifikus kódegységekre vezeti le.

## Tensor entitás kapcsolatok

### Memóriakezelés és COW

A JAIDE egy Copy-On-Write (COW) mechanizmust valósít meg az atomikus hivatkozásszámlálással kombinálva, hogy minimalizálja a szükségtelen adatduplikációt, miközben biztosítja a szálbiztonságot.

1.   Referenciaszámlálás: Amikor egy tenzor megosztásra kerül (pl. retain() segítségével), a refcount egy atomi fetch-add művelet segítségével növekszik
2.   COW Trigger: A retain() hívása a tehén jelzőt igazra állítja
3.   Menetbiztonság: A stressztesztek ellenőrzik, hogy az egyidejű megtartási és feloldási műveletek konzisztens állapotot tartanak fenn több szálon keresztül a .seq_cst atomi sorrendezéssel
4.   Automatikus felszabadítás: Amikor a release() meghívásra kerül, és a referenciaszám eléri a nullát, a mögöttes adatok, a refcount és a tehénmutatók felszabadulnak

### Tensor műveletek

### TensorIterator

Nem összefüggő nézetek esetén (amelyek szeletekből vagy összetett lépésekből származnak), a TensorIterator egy mechanizmust biztosít a tenzoradatok logikai sorrendben történő átfutásához Fenntart egy belső offset és index tömböt az egyes többdimenziós koordináták lapos memóriacímének kiszámításához

### Lineáris algebra

A rendszer speciális implementációkat tartalmaz a mátrixműveletekhez:

- MatmulComptime: Mátrix szorzás fix dimenziókra
- SIMD gyorsítás: A rendszer definiál egy Vec8 típust a @Vector(8, f32) használatával, hogy kihasználja a SIMD utasításokat az elemenkénti műveletekhez

### Fixpont-támogatás

Míg az elsődleges Tensor f32-t használ, a rendszer a types.zig modulon keresztül támogatja a fixpontos aritmetikát a speciális hardver vagy pontossági követelmények esetén:

- FixedPoint16: 8 bites tört rész
- FixedPoint32: 16 bites tört rész
- Fixed32_32: 32 bites tört rész i64 használatával

### Adatáramlás: Tensor művelet küldése

Ez az ábra azt szemlélteti, hogy a memóriaelrendezés és a hardver képességei alapján hogyan történik egy tenzorművelet.

## Tensor művelet adatáramlás

### Inicializálás és allokátorok

A tenzorok inicializálhatók a memória alrendszerben definiált különböző egyéni allokátorokkal:

- Szabványos: Init(allokátor, dims)
- Aréna: InitWithArena(arena, dims)
- Medence: Tensor.initWithPool(pool, dims)
- Födém: Tensor.initWithSlab(slab, dims)
- Buddy: Tensor.initWithBuddy(buddy, dims)

Az AVX/SIMD utasításokkal való kompatibilitás érdekében minden allokáció 32 bájtos igazítású

## Memóriakezelés

A memóriakezelő alrendszer nagy teljesítményű, szálbiztos és biztonságos kiosztási csomagot biztosít a JAIDE architektúrára szabva. Különböző allokációs stratégiákat (Arena, Slab, Pool, Buddy) valósít meg a fragmentáció és a késleltetés minimalizálása érdekében, valamint kriptográfiai segédprogramokat az érzékeny adatok kezelésére.

### Alapfelosztók

A JAIDE speciális allokátorokat használ a különböző objektum-életciklusok és memória-hozzáférési minták kezelésére.

### Aréna és ArenaAllocator

Az Arena struktúra egy fix méretű, szálbiztos memóriablokkot biztosít, ahol a kiosztás egyszerű mutató inkrementálással történik. Rövid életű feladatokhoz használják, ahol az összes memória egyszerre visszakövetelhető Az ArenaAllocator ezt több dinamikus puffer kezelésével bővíti, amelyek szükség szerint nőnek, és megvalósítják az std.mem.Allocator interfészt

### Födém és medence elosztók

A kis, fix méretű objektumok (például gráfcsomópontok vagy tenzormetaadatok) gyakori kiosztásához a JAIDE a SlabAllocator és a PoolAllocator programokat használja.

- SlabAllocator: Egyenlő méretű memóriarészekre osztott "tábla" memóriát kezel. A szabad slotokat bitmaszk vagy összekapcsolt lista segítségével követi, hogy biztosítsa a $O(1)$ ki- és visszahelyezést egy slabon belül.
- PoolAllocator: Egyetlen típus nagy gyakoriságú kiosztására optimalizált, előre kiosztott példányok pooljának fenntartása az általános célú kiosztó rezsiköltségének megkerülése érdekében.

### Buddy és Page Allocators

- BuddyAllocator: A nagyobb, változó méretű blokkok kezelésére szolgál. A memóriát két hatványra osztja, hogy megtalálja a legkisebb blokkot, amely megfelel a kérésnek, megkönnyítve a hatékony összevonást (coalescing), amikor a blokkok felszabadulnak.
- PageAllocator: Közvetlenül az operációs rendszerrel (a min_page_align-on keresztül), hogy oldalszintű memóriát kérjen (jellemzően 4KB vagy 16KB, architektúrától függően)

### Rendszerentitás-leképezés

A következő ábra a magas szintű memóriafogalmakat a magkönyvtárban megvalósított specifikus Zig-egységekhez rendeli hozzá.

Memória entitás térkép

### Biztonságos memória segédprogramok

A biztonságot a memóriarétegbe integráltuk, hogy megakadályozzuk az érzékeny modellsúlyok vagy API-kulcsok adatszivárgását.

| Funkció | Cél | Megvalósítás részletei |
| --- | --- | --- |
| secureZeroMemory | Memóriarégiók törlése. | Megakadályozza, hogy a fordítóoptimalizálás kihagyja az érzékeny adatok nullázását |
| secureErase | Biztonságosan törli a kiosztást. | Kombinálja a secureZeroMemory-t a mögöttes free hívással. |
| ChaCha20Poly1305 | Memórián belüli titkosítás. | Olyan érzékeny memóriaszegmensek titkosítására szolgál, amelyeket a CPU éppen nem használ. |

Az Arena és az ArenaAllocator implementálja a secureReset funkciót, amely biztosítja, hogy az összes korábban kiosztott bájt nullázásra kerüljön, mielőtt az eltolás visszaállításra kerül

### Egyidejűség és szinkronizálás

A többszálú képzés és következtetés támogatása érdekében a memóriarendszer zár alapú és zár nélküli primitíveket egyaránt alkalmaz.

### ReadWriteLock

A ReadWriteLock több egyidejű olvasót, de az írók számára kizárólagos hozzáférést biztosít. Ez kritikus az RSFLayer esetében, ahol a súlyokat gyakran olvassák az előrehaladáshoz, de az optimalizáló ritkán frissíti őket

### Zármentes szerkezetek

A JAIDE zárolásmentes várólistákat és halmokat valósít meg atomi műveletekkel, hogy a CPU és a GPU-koordinációs szálak közötti nagy teljesítményű kommunikációt megkönnyítse a mutex-konfliktus okozta többletköltségek nélkül.

Kiosztási adatáramlás

### Nyomon követés és diagnosztika

A TrackingAllocator egy olyan wrapper, amely figyeli a memóriahasználati mintákat.

- Kiosztás nyomon követése: Az aktív allokációk számát és az összes felhasznált bájtot rögzíti.
- Szivárgásérzékelés: A hibakeresés során azonosítani tudja a deinit során fel nem szabadított memóriát.
- Kiegyenlítés ellenőrzése: Biztosítja, hogy minden kiosztás megfeleljen a SIMD műveletek és a hardveres korlátozások követelményeinek

### Konfigurációs konstansok

A rendszer szabványos méreteket határoz meg a hardveres gyorsítótárakhoz és a laphatárokhoz való igazodás érdekében:

- PAGE_SIZE: Az operációs rendszer és az architektúra határozza meg (4KB x86 esetén, 16KB Apple Silicon esetén)
- CACHE_LINE_SIZE: 128 bájtra állítva, hogy megakadályozza a hamis megosztást többszálú kontextusokban

## I/O és modellmegmaradás

Ez a szakasz a JAIDE alapvető I/O segédprogramjaival és a modell szerializálási keretrendszerével foglalkozik. A rendszer egyedi bináris formátumot használ a modell perzisztenciájához, kihasználva a memóriaközpontú fájlokat a teljesítmény és a CRC32 ellenőrző összegeket az adatok integritása érdekében. Az architektúra hangsúlyt fektet az atomi műveletekre és a biztonságos memóriakezelésre, hogy biztosítsa a modell robusztus telepítését és a képzési állapot megőrzését.

### Fájl I/O és memória leképezés

A core/io.zig modul nagy teljesítményű fájlműveleteket biztosít az MMAP struktúra körül. Ez az absztrakció lehetővé teszi a rendszer számára, hogy a fájlokat memóriapufferként kezelje, megkönnyítve a nagy modellsúlyokhoz és indexekhez való gyors hozzáférést.

### MMAP végrehajtása

Az MMAP struktúra kezeli a memória leképezett régiók életciklusát, támogatva a csak olvasható és az írható módot is:

- Atomikus átméretezés: Az append funkció a fájl növekedését a leképezés feloldásával, az alapul szolgáló fájl kiterjesztésével és az új régió újbóli leképezésével kezeli
- Menetbiztonság: Thread.Mutex védi a pufferhez való hozzáférést
- Szinkron perzisztencia: Támogatja az explicit msync hívásokat az adatok fizikai tárolóba történő kiürítésének biztosítása érdekében

### Konfiguráció és hibakezelés

Az I/O műveleteket az IoConfig szabályozza, amely konstansokat határoz meg a puffer méretére, az útvonal hosszára és a biztonsági módokra vonatkozóan A hibák szemcsések, a BufferNotMapped-től a PathTooLong-ig terjedő eseteket fedik le

### I/O logikai áramlás

A következő ábra a fájlrendszer és az MMAP absztrakció közötti kölcsönhatást szemlélteti.

### Modell szerializáció (RSF0 és JAIDE40)

A JAIDE két elsődleges formátumot használ a perzisztenciához: az RSF0 formátumot az egyes Reversible Scatter Flow rétegekhez és a JAIDE40 konténer formátumot a teljes modell pillanatfelvételekhez.

### A JAIDE40 konténer

Az src/core/model_io.zig fájlban található ModelFormat struktúra a teljes modellek mentésének és betöltésének elsődleges szervezője

- Mágikus fejléc: A fájlok a JAIDE40\x00 bájtsorozattal kezdődnek
- Metaadatok: A modell konfigurációja (rétegek száma, méretek, vocab méret) JSON kódolású blokkként tárolódik a bináris fájlban
- Integritás: A rendszer CRC32 ellenőrző összegeket használ a komponensek integritásának ellenőrzésére a deserializálás során

### Atomi perzisztencia

Az összeomlások során bekövetkező modellrongálódás megelőzése érdekében a JAIDE egy atomi írási-az-újraelnevezési stratégiát alkalmaz. A modelleket először egy ideiglenes fájlba (pl. model.bin.tmp) írja, majd az írás és a szinkronizálás sikerességének megerősítése után átnevezi a végső célállomásra.

### Modell metaadatok szerkezete

| Mező | Típus | Leírás |
| --- | --- | --- |
| model_name | []const u8 | A modell egyedi azonosítója |
| version | u32 | Format version (jelenleg 1) |
| rsf_layers | usize | Az RSF rétegek száma az architektúrában |
| mgt_vocab_size | usize | Az MGT tokenizáló szókincs mérete |

### Tanult beágyazások

A LearnedEmbedding modul kezeli a tokenek betanítható vektorreprezentációit. Közvetlenül integrálódik a tenzorrendszerrel a gradiens alapú frissítésekhez.

### A végrehajtás részletei

- Inicializálás: A súlyok inicializálása egy PRNG segítségével történik, egy adott maggal, amely általában 0,02-vel skálázódik a variancia fenntartása érdekében
- Előre passz: A bemeneti tokeneket a súlytenzor megfelelő soraihoz rendeli
- Visszafelé passz: A gradiensek felhalmozása egy grad tenzorba a backpropagáció során megadott out_grad alapján
- Optimalizálás: Az applyGradients függvény egy alapvető SGD frissítést hajt végre lendülettel

### Kitartás

A beágyazások egy speciális bináris formátumban kerülnek elmentésre a 0x4A454D42 (JEMB) mágikus fejléccel. A formátum tartalmazza a szókincs méretét és a beágyazási dimenziót, amelyet a nyers f32 súlyok követnek

### A legfontosabb funkciók összefoglalása

| Modul | Funkció | Szerep |
| --- | --- | --- |
| core/io.zig | MMAP.open | Letölt egy fájlt a memóriába a zéró másolású hozzáféréshez |
| core/io.zig | mixHash | Finalizer a belső hashing segédprogramokhoz |
| core/model_io.zig | ModelMetadata.fromJson | A modell konfigurációjának deserializálása JSON-ból |
| core/learned_embedding.zig | save | Beágyazási súlyok sorba rendezése a lemezre |
| core/learned_embedding.zig | forward | Beágyazási keresést végez a token szekvenciákhoz |

## RSF feldolgozási csővezeték

### "Nyitott adattár")

Devin

Utolsó indexálás: 2026. május 10. (

Menü

### RSF feldolgozási csővezeték

A JAIDE rendszer alapvető neurális architektúrája a Reversible Scatter Flow (RSF) feldolgozási csővezeték. Úgy tervezték, mint egy bijektív (invertálható) transzformációs szekvenciát, amely a bemeneti adatokat egy látens térbe képezi le, miközben a képzés során O(1) visszaterjedésen keresztül állandó memóriaigényt tart fenn. A hagyományos neurális hálózatokkal ellentétben, amelyek az aktivációkat a visszafelé haladáshoz tárolják, az RSF menet közben rekonstruálja azokat az egyes rétegek inverzének felhasználásával.

A csővezeték váltakozó RSFLayers (affin csatolás) és OFTB blokkokból (ortogonális keverés) áll, amelyeket az SFD (Stochastic Fisher Diagonal) optimalizálóval optimalizálnak.

### Rendszerarchitektúra áttekintése

A csővezeték 2D-s tenzorokkal dolgozik, amelyek jellemzően szekvenciák kötegeit reprezentálják. A transzformációt reverzibilis műveletek sorozata határozza meg, ahol az előremenő $y = f(x)$ átmenetnek van egy megfelelő pontos inverze $x = f^{-1}(y)$.

### RSF réteg: Affin csatolás

Az RSFLayer egy bijektív csatolási mechanizmust valósít meg. A bemeneti tenzort két félre osztja; az egyik fele változatlan marad, és a skála- ($s$) és transzlációs ($t$) paraméterek kiszámítására szolgál, amelyek a második felet átalakítják. Ez a struktúra biztosítja, hogy a jakobián alsó háromszögű legyen, így a determináns (és így a log-likelihood) triviálisan kiszámítható.

A legfontosabb jellemzők:

- In-Place műveletek: a forwardInPlace és inverseInPlace közvetlenül módosítja a tenzorokat, hogy minimalizálja a kiosztást
- Memóriahatékonyság: A backwardFromOutputsRow módszer használatával a réteg a gradienseket a köztes aktiválások tárolása nélkül tudja kiszámítani
- Stabilitás: Használ konfigurálható clip_min és clip_max értékeket, hogy megakadályozza az exponenciális robbanást a skála transzformációban

A részletekért lásd

### OFTB: Ortogonális fraktál transzformációs blokk

Az OFTB (Orthogonal Fractal Transform Block) paramétermentes keverést biztosít a tenzor dimenziói között. Haar-wavelet pillangószerkezetet használ annak biztosítására, hogy az összes bemeneti csatornából származó információ szétterjedjen a látens térben.

- Fraktál skálázás: FRACTAL_SCALE (kb. 0,7071) konstansot használ, hogy az egységnyi variancia a transzformációk között megmaradjon
- SIMD gyorsítás: A megvalósítás a Zig @Vector(8, f32) funkcióját használja a modern CPU-kon történő nagy teljesítményű feldolgozáshoz
- Ortogonalitás: A transzformáció a saját skálázott transzponálása, ami biztosítja, hogy a művelet könnyen visszafordítható legyen a visszamenőleges lépés során

A részletekért lásd

### SFD optimalizáló

A Stochastic Fisher Diagonal (SFD) optimalizálót kifejezetten az RSF architektúrára hangolták. A természetes gradienst a Fisher-információs mátrix diagonálisának becslésével közelíti meg.

- Görbületbecslés: Hutchinson-stílusú Hessian becslést és Kronecker-faktorált görbületet (KFAC) használ a paraméterenkénti tanulási arányok adaptálásához.
- Vegyes precizitás: Integrálódik a MixedPrecisionTrainerrel az FP16/BF16 hardveres gyorsítás kihasználása érdekében, az FP32 master súlyok fenntartása mellett.
- Állami irányítás: ReversibleOptimizerState, amely lehetővé teszi, hogy magát az optimalizálót minimális overheaddel lehessen ellenőrizni és visszaállítani.

A részletekért lásd

### Kód Entitás leképezés

Az alábbi ábra az RSF-csatorna logikai összetevőit a Zig forráskódjában található konkrét megvalósításukhoz rendeli.

### A csővezeték végrehajtási életciklusa

A csővezetéket jellemzően egy modell vagy oktató kezeli, amely az adatáramlást a rétegeken keresztül irányítja.

| Fázis | Módszer | Leírás |
| --- | --- | --- |
| Inicializálás | RSFCore.init | Xavier/Kaiming inicializálással osztja ki a súlyokat a $s$ és $t$ hálózatokhoz. |
| Következtetés | forwardInPlace | Az RSFLayer és az OFTB transzformációkat egymás után alkalmazza a bemenetre. |
| Inverzió | inverseInPlace | Megfordítja a transzformációkat, hogy a látens kódokból rekonstruálja a bemeneteket. |
| Training | backwardFromOutputsRow | Paramétergradiensek kiszámítása a rekonstruált aktivációk felhasználásával. |

Elutasíthatod

Frissítse ezt a wikit

Ez a wiki nemrégiben frissült. Kérjük, várjon 7 napot az újbóli frissítéshez.

### Ezen az oldalon

## RSF réteg: Előre, inverz és visszafelé haladások

A Reversible Scatter Flow (RSF) réteg a JAIDE architektúra alapvető bijektív transzformációs egysége. Olyan affin csatolási mechanizmust valósít meg, amely biztosítja az invertibilitást és a $O(1)$ memóriás visszaterjedést azáltal, hogy az aktivációkat a visszaterjedés során rekonstruálja, ahelyett, hogy tárolná őket.

### RSF architektúra áttekintése

Az RSF réteg egy két részre ($x_1, x_2$) osztott 2D tenzorral dolgozik. A transzformációt skála ($S$) és transzlációs ($T$) függvények határozzák meg, amelyeket jellemzően neurális súlyokkal paramétereznek.

| Component | Entitás a kódban | Role |
| --- | --- | --- |
| Konfiguráció | RSFLayerConfig | Meghatározza a vágási tartományokat és a gradiens skálázást |
| Súlytárolás | LayerCore | $S$ és $T$ súlyok, torzítások és opcionális gradiensek |
| Logikai motor | RSFCore | Alacsony szintű matematika a soronkénti skálázáshoz/fordításhoz és gradiensekhez |
| Állapotkezelő | RSFLayer | Magas szintű API szálbiztos RwLock-kal és GPU-diszpécserrel |

### Matematikai megvalósítás: Affin csatolás

Az RSF réteg bijektív leképezést használ, ahol a bemenet egyik fele változatlan marad, és a második felének átalakításához szükséges paraméterek kiszámítására szolgál.

### 1. Előre passz

$x_1, x_2$ bemenetek esetén:

- $y_1 = x_1$
- $y_2 = x_2 \cdot \exp(\text{clip}(S(x_1))) + T(x_1)$

### 2. Inverz passz

A bemenetek rekonstruálása a $y_1, y_2$ kimenetekből:

- $x_1 = y_1$
- $x_2 = (y_2 - T(y_1)) \cdot \exp(-\text{clip}(S(y_1)))$

### Soronkénti műveletek

Az alapvető matematikai feladatokat az RSFCore-ban soronkénti függvények használatával valósítottuk meg a SIMD optimalizálás és a tételek közötti párhuzamos feldolgozás megkönnyítése érdekében.

- computeScaleRow: Kiszámítja $s = x_1 \cdot W_s + b_s$, majd a clip_min és clip_max által meghatározott vágási művelet következik
- computeTranslationRow: Kiszámítja $t = x_1 \cdot W_t + b_t$

### Adatáramlás és rendszerintegráció

A következő ábra a magas szintű "természetes nyelvi térből" (architektúrális fogalmak) a "kódegység-térbe" (konkrét Zig-struktúrák és funkciók) való átmenetet szemlélteti.

RSF végrehajtási csővezeték

### Helyszíni műveletek és memóriabiztonság

Az allokációk minimalizálása érdekében az RSFLayer forwardInPlace és inverseInPlace módszereket biztosít. Ezek a függvények egy RwLock-ot használnak a szálbiztonság biztosítására a súlyfrissítések során, miközben lehetővé teszik az egyidejű következtetést.

### Nyilvántartási fogantyú életciklusa

A rendszer az RSFLayer példányokat egy nyilvántartáson keresztül kezeli.

1.   Kiosztás: RSFLayer.init kiosztja a LayerCore-t és inicializálja a súlyokat a Xavier inicializálással
2.   Hozzáférés: A komponensek egy fogantyút kérnek, ami növeli a hivatkozások számát.
3.   Felosztás: Deinit biztosítja, hogy a súlyok és torzítások összes Tensor memóriája visszaszabaduljon az Allocatorhoz

### GPU/CPU-diszpécser

Az RSFLayer absztrahálja a végrehajtási háttértárat. Ha rendelkezésre áll egy GPU, és az accel interfész inicializálva van, a réteg a Futhark kerneleknek küldi a munkát. Ellenkező esetben SIMD-gyorsítású CPU kódra esik vissza

### Visszafelé haladási és gradiens számítás

A backwardFromOutputsRow függvény a $O(1)$ memóriaképzés motorja. Mivel a réteg reverzibilis, az eredeti $x_1, x_2$ bemeneteket a $y_1, y_2$ kimenetekből rekonstruáljuk a visszafelé lépés során.

Gradiens áramlás:

1.   Rekonstrukció: $x_1$ és $x_2$ az inverz logika segítségével nyerhető vissza.
2.   Helyi gradiensek:
- $\frac{\partial L}{\partial S}$ a skála exponenciálisából származik.
- $\frac{\partial L}{\partial T}$ a fordítási összeadásból származik.

3.   Súlyfrissítés: A gradiensek a LayerCore-on belül az s_weight_grad és a t_weight_grad értékekben halmozódnak fel

### RSF0 Sorozatba rendezési formátum

A modelleket az RSF0 bináris formátumban tárolják. Ez a formátum a visszafelé kompatibilitás biztosítása érdekében verziószámmal van ellátva (jelenlegi SAVE_VERSION: 4).

| Offset | Mező | Típus | Leírás |
| --- | --- | --- | --- |
| 0x00 | Magic Header | [4]u8 | Mindig "RSF0" |
| 0x04 | Verzió | u32 | Jelenlegi verzió (4) |
| 0x08 | Méretek | u64 | Jellemző dimenzió mérete |
| 0x10 | Rétegszám | u64 | A kapcsolási rétegek száma |
| 0x18+ | Súlyadatok | f32[] | Nyers tenzoradatok a S/T súlyokhoz és torzításokhoz |

RSF szerializációs logika

## OFTB: Ortogonális fraktál transzformációs blokk

Az Orthogonal Fractal Transform Block (OFTB) egy paramétermentes keverési réteg a JAIDE RSF csővezetéken belül. Egy bijektív, ortogonális Haar-wavelet pillangó transzformációt valósít meg, amelyet úgy terveztek, hogy a tenzor dimenzióinak globális jellemzőkeverését biztosítsa további tanulható súlyok bevezetése nélkül. Ez biztosítja, hogy a transzformáció egyszerre memóriahatékony és eredendően stabil a backpropagáció során.

### Cél és tervezés

Az OFTB a jellemzőtérben rögzített forgatásként működik. A FRACTAL_SCALE konstans (1/√2) felhasználásával a blokk fenntartja a bemeneti vektor normáját, biztosítva, hogy a transzformáció ortogonális legyen. Ez a tulajdonság kritikus fontosságú a Reversible Scatter Flow (RSF) architektúra számára, mivel lehetővé teszi a pontos inverziót és a stabil gradiensáramlást a mély kapcsolási rétegek halmazain keresztül.

### Legfontosabb matematikai tulajdonságok

Az OFTB egy $2N$ dimenziójú bemeneti vektort két félre, $x_1$ és $x_2$ méretű, $N$ méretű részre bont. Ezután a következő pillangó transzformációt alkalmazza:

Előrehaladás: $$x_1' = (x_1 - x_2) \cdot \text{FRACTAL_SCALE}$$ $$x_2' = (x_1 + x_2) \cdot \text{FRACTAL_SCALE}$$$

Visszafelé passzolás (inverz): $$g_1' = (g_1 + g_2) \cdot \text{FRACTAL_SCALE}$$ $$g_2' = (g_2 - g_1) \cdot \text{FRACTAL_SCALE}$$$

### Végrehajtás részletei

Az src/processor/oftb.zig állományban található OFTB struktúra biztosítja az ilyen átalakítások alaplogikáját. A modern CPU-kra optimalizálták a Zig @Vector SIMD primitívek használatával.

### Szerkezet és inicializálás

Az OFTB csak annak a félvektornak a dimenzióját tárolja, amelyen dolgozik.

| Mező | Típus | Leírás |
| --- | --- | --- |
| dim | usize | A bemeneti tenzor egyik felének mérete (a teljes bemeneti méret dim 2). |

Az init függvény biztonsági ellenőrzéseket végez annak biztosítására, hogy a dimenzió nem nulla és nem okoz túlcsordulást, ha megduplázódik

### SIMD vektorizáció

Mind a forwardInPlace, mind a backwardInPlace 8-as vektorhosszúságot használ (@Vector(8, f32)). A megvalósítás a "SIMD skaláris visszaeséssel" mintát követi:

1.   Vektorhurok: 8 f32 elemű darabok feldolgozása SIMD utasításokkal
2.   Scalar Fallback: A fennmaradó elemeket (ahol fél % 8 != 0) egyenként dolgozza fel

### Adatáramlás: előre és hátrafelé

Az alábbi ábra szemlélteti az OFTB-módszerek és a mögöttes Tensor adatstruktúrák közötti kapcsolatot.

Az OFTB logika és a kódegységek közötti leképezés

### Integráció az RSF csővezetékkel

Az OFTB keverési lépésként beépül az RSF (Reversible Scatter Flow) csővezetékbe. Mivel paramétermentes, nem igényel optimalizáló frissítést, de a gradienseket helyesen kell továbbítania a visszafelé haladás során.

### Biztonsági és méretellenőrzés

A megvalósítás szigorú korlátok ellenőrzését alkalmazza a memóriakárosodás megelőzése érdekében:

- InvalidDimension: Ha dim == 0, hibát ad vissza
- DimensionOverflow: Hiba, ha dim 2 meghaladja az usize kapacitást
- TensorTooSmall: Biztosítja, hogy a megadott Tensor vagy gradiens szelet legalább dim 2 elemű legyen

### Komponensek kölcsönhatása

A következő ábra azt mutatja, hogy az OFTB hogyan lép kölcsönhatásba a Tensor rendszerrel és a tágabb RSF folyamattal.

OFTB csővezeték integráció

### Formális ellenőrzés (Lean 4)

Az OFTB pillangó matematikai helyessége formálisan az src/verification/lean4/oftb.lean dokumentumban van ellenőrizve. A verifikációs csomag definiál egy fixpontos aritmetikai modellt (FP), és bizonyítja a transzformáció invertálhatóságát és skálázhatósági tulajdonságait.

### Ellenőrzött állandók

A Lean 4 specifikáció a fraktálskálát nagy pontosságú egész számokkal ábrázolja:

- skála: 100000000 (1.0)
- fractalScale: 70710678 (≈ 0.7071)
- halfFractalScale: 35355339 (≈ 0.3535)

### Ellenőrzési tételek

A bizonyítások biztosítják, hogy a pillangó-transzformáció megőrzi az olyan speciális algebrai tulajdonságokat, mint a kommutativitás és asszociativitás a fixpontos korlátozásokon belül, amelyek elengedhetetlenek a forwardInPlace és backwardInPlace módszerek numerikus stabilitásához.

### API-hivatkozás

### OFTB módszerek

| Funkció | Leírás |
| --- | --- |
| init(d: usize) OFTB | Egy d féldimenziós blokk inicializálása. Állítja, hogy d > 0. |
| forwardInPlace(x: Tensor) !void | Elvégzi a forward pillangó transzformációt a tenzor első 2dim elemein. |
| backwardInPlace(grad: []f32) !void | Elvégzi az adjungált pillangó transzformációt egy gradiens szeleten. |
| backwardInPlaceSlice(grad: []f32) !void | A backwardInPlace alias neve a szelet alapú hívók számára. |
| deinit() | Érvényteleníti az OFTB-példányt. |

## SFD optimalizáló

A Stochastic Fisher Diagonal (SFD) optimalizáló egy nagy teljesítményű másodrendű optimalizáló motor, amelyet a JAIDE architektúrához terveztek. A Fisher Information Matrix (FIM) becslést a SophiaSOAP kiterjesztéssel kombinálja, hogy görbületet figyelembe vevő frissítéseket biztosítson, amelyek nem konvex tájakon felülmúlják a standard elsőrendű módszereket, mint például az Adam. A rendszer fejlett memóriakezelést integrál az NVIDIA B200-osztályú hardverhez, vegyes pontosságú képzést és Bayes-féle hiperparaméter-optimalizálást.

### Az SFD végrehajtásának áttekintése

Az optimalizáló magja az src/optimizer/sfd.zig állományban található. Fenntartja a Fisher Információs Mátrix diagonális közelítését a gradiensek skálázásához, gyakorlatilag egyfajta természetes gradiens leszállással.

### Főbb összetevők

| Komponens | Leírás | Kódegység |
| --- | --- | --- |
| SFD Optimizer | Fő optimalizáló állapot és frissítési logika. | SFDOptimizer |
| Fisher-diagonális | A FIM-diagonális sztochasztikus becslése. | SFDOptimizer.updateFisher | SFDOptimizer.updateFisher |
| SophiaSOAP | Másodrendű kiterjesztés Hutchinson Hessian becsléssel. | SophiaSOAP |
| KFAC Block | Kronecker-faktorált közelítő görbület rétegek számára. | KFACBlock |
| Vegyes pontosság | FP4, FP8, FP16 és FP32 képzéshez való kezelés. | MixedPrecisionTrainer |

### SFD adatáramlás

A következő ábra a gradiens számítástól a paraméterek frissítéséig tartó folyamatot mutatja be az SFD és a SophiaSOAP logika segítségével.

Optimalizáló frissítési csővezeték

### Sztochasztikus Fisher-diagonális és KFAC

Az SFDOptimizer a Fisher Információs Mátrix diagonálisát követi a négyzetes gradiensek mozgó átlagának segítségével A bonyolultabb rétegfüggőségek esetén a KFACBlock Kronecker-faktoros közelítést biztosít, amely számítási szempontból hatékonyabb, mint a teljes Hessian, miközben megragadja a diagonálison kívüli görbületet

### Hutchinson Hessian becslés

A HutchinsonEstimator Rademacher vagy Gauss zajvektorokat használ a Hessian nyomvonalának becslésére a mátrix explicit képzése nélkül

- Módszer: estimateHessianDiagonal becslése
- Zajgenerálás: fillRademacher

### SophiaSOAP kiterjesztés

A SophiaSOAP osztály egy "másodrendű sztochasztikus optimalizálás minden paraméterrel" megközelítést valósít meg. A HutchinsonEstimator-t használja, hogy diagonális Hess-becslést adjon, amelyet a frissítések levágására és skálázására használ

### Képzési segédprogramok

### Vegyes pontosság és veszteség skálázás

A MixedPrecisionTrainer különböző bitszélességű tenzorokat kezel (Precision enum: fp4, fp8, fp16, fp32, fp64) Az alacsonyabb pontosságú tenzorok alulcsordulásának megelőzése érdekében a DynamicLossScaler a veszteség skálafaktort a NaN vagy Inf értékek gradiensekben való jelenléte alapján állítja be

### B200 memóriakezelés

A B200MemoryManager egy speciális allokátor, amelyet a Blackwell-architektúrájú GPU-k nagy sávszélességű memóriájához (HBM) terveztek. Kezeli a memória kitűzését és a blokkalapú kiosztást, hogy minimalizálja a töredezettséget a nagyméretű képzés során

### Bayes-optimalizáló

A hiperparaméterek (pl. tanulási sebesség, lendület) hangolásához a BayesianOptimizer Gauss-folyamatokat használ a célfüggvény modellezésére

- Beszerzési funkció: Várható javulás (EI) az erfApprox segítségével számítva

### Rendszerentitás-leképezés

A következő ábra a logikai optimalizáló komponenseket az src/optimizer/sfd.zig fájlban található implementációs struktúrákhoz rendeli.

Entitás leképezési diagram

### Visszafordítható optimalizáló állapot

A JAIDE O(1) memória visszaterjedésének támogatása érdekében a ReversibleOptimizerState lehetővé teszi az optimalizáló belső állapotának (mint például a momentum pufferek) rekonstruálását vagy visszafordítását a Reversible Scatter Flow (RSF) rétegek visszaterjedése során

### Kulcsfunkciók

- saveState: Pillanatképeket készít az aktuális Fisher és momentum pufferekről
- revertState: Visszaállítja a puffereket egy korábbi verzióra, biztosítva a konzisztenciát az aktiválások újbóli kiszámításakor

## Tokenizáló és visszakeresés

A Tokenizer & Retrieval alrendszer biztosítja az interfészt a természetes nyelvi bemenet és az RSF csővezeték által feldolgozott nagydimenziós tenzortér között. Magában foglalja a morfológiai szövegbontást, a szekvenciák tárolására szolgáló strukturált indexelési mechanizmust és a hasonlósági kereséshez szükséges többtényezős rangsoroló motort.

### A csővezeték áttekintése

A csővezeték a nyers szöveget az MGT Tokenizer segítségével diszkrét tokenekké alakítja, amelyeket aztán a strukturált szekvenciaindex (SSI) indexel vagy lekérdez. A rangsoroló az n-gram átfedés, a diverzitás és a közelség metrikái alapján értékeli a lekérdezett szegmensek relevanciáját.

A Morpheme-Guided Tokenizer (MGT) egy hibrid kódolómotor, amelyet nyelvileg gazdag nyelvek számára terveztek (angol és magyar nyelv támogatása). A standard BPE-vel ellentétben a morfológiai bontást előtagokra, gyökökre és utótagokra helyezi előtérbe, mielőtt visszalépne az alszavak összevonására.

- Hibrid csővezeték: [PAD], [BOS]), szóközöket és írásjeleket, mielőtt morfológiai szabályokat alkalmaznánk
- Morfémalisták: Belső hash-térképeket tart fenn a gyakori előtagok és utótagok számára, hogy javítsa a tokenhatárok felismerését
- Horgonykövetés: Támogatja a "horgonyokat" - nagy jelentőségű tokeneket, amelyek referenciapontként szolgálnak a keresőrendszer számára

A részletekért lásd

A strukturált szekvenciaindex (SSI) egy vödöralapú fa struktúra, amelyet nagy teljesítményű szekvencia-visszakeresésre terveztek. Olyan szegmensadatokat tárol, amelyek token szekvenciákat társítanak pozíciójukkal és pontszámukkal.

- Adatmodell: A gyors kereséshez egy Segment struct-ot használ a token szeletek, a pozíció metaadatok és egy anchor_hash tárolására
- Integritás: A Merkle-szerű hash-sémát alkalmazza, ahol minden csomópont fenntartja gyermekeinek vagy szegmenseinek hash-jét, lehetővé téve a gyors konzisztencia-ellenőrzést
- Ütközéskezelés: CollisionNode láncokat használ az index vödrökön belüli hash ütközések kezelésére

A részletekért lásd

A rangsoroló biztosítja az SSI-ből lekérdezett szekvenciák sorrendbe állításához használt pontozási logikát. A klasszikus statisztikai módszereket modern hasonlósági metrikákkal kombinálja.

- Pontszámítási mérőszámok: Kombinálja az n-gram pontszámokat csökkenő súlyokkal, token diverzitás arányokkal és horgonyok közelségével
- Hasonlósági motorok: Jaccard hasonlóság (AutoHashMap vagy BitSet segítségével) és Cosine hasonlóság a lekérdezési vektorok és az indexelt szegmensek összehasonlításához
- Párhuzamosítás: A párhuzamosScore műveletekhez egy szálkészletet használ a nagyméretű lekérdezési feladatok hatékony kezelése érdekében.

A részletekért lásd

### Rendszerintegrációs diagram

Ez az ábra azt szemlélteti, hogy a rangsoroló hogyan működik az MGT tokenizáló és az SSI index között, hogy a neurális rétegek számára bemenetet állítson elő.

## MGT Tokenizer

A Morpheme-Guided Tokenizer (MGT) egy hibrid kódoló csővezeték, amelyet a JAIDE architektúrához terveztek. A hagyományos Byte-Pár kódolást (BPE) kombinálja a kifejezetten a magyar és az angol nyelvi struktúrákra hangolt morfológiai dekompozícióval. A standard alszavas tokenizátorokkal ellentétben az MGT az előtagokat, gyököket és utótagokat helyezi előtérbe, hogy az agglutinatív és fuzionatív nyelvhatárokon keresztül is megőrizze a szemantikai integritást.

### 1. A csővezeték áttekintése

Az MGT kódolási folyamat egy többlépcsős csővezetéket követ, hogy a nyers természetes nyelvet az RSF-feldolgozó csővezeték számára alkalmas diszkrét tokenazonosítókká alakítsa át.

### Kódolási szakaszok

1.   Különleges token-azonosítás: Előre meghatározott vezérlőjegyek keresése (pl. [BOS], [EOS]).
2.   Fehér tér/pontozás szétválasztása: Alapvető előjelzés szószerű egységekre.
3.   Morfológiai bontás: Megpróbálja az egységeket ismert előtagokra, gyökökre és utótagokra bontani.
4.   BPE Fallback: A morfológiai szabályok által nem lefedett egységek esetében a tanult gyakoriságok alapján iteratív párösszevonást alkalmaz.
5.   Horgonykövetés: Az SSI-ben (Structured Sequence Index) a relációs leképezéshez használt "horgonyzó" tokenek azonosítása és címkézése.

### Természetes nyelv az entitás tér kódolásához

A következő ábra a nyelvi fogalmakat az mgt.zig implementációban található konkrét adatstruktúrákhoz és funkciókhoz rendeli hozzá.

Nyelvi és végrehajtási feltérképezés

### 2. Alapvető végrehajtás

### Az MGT szerkezete

Az MGT struktúra kezeli a szókincs életciklusát és a morfológiai listák állapotát. Több std.StringHashMap példányt használ a tokenek és szerepeik O(1) kereséséhez.

| Mező | Típus | Leírás |
| --- | --- | --- |
| token_to_id | StringHashMap(u32) | A karakterlánc-tokeneket numerikus azonosítókra képezi le. |
| id_to_token | AutoHashMap(u32, []const u8) | Inverz leképezés a dekódoláshoz. |
| prefixes | StringHashMap(u32) | Morfológiai prefixek listája (pl. "un", "meg"). |
| suffixes | StringHashMap(u32) | Morfológiai szuffixumok listája (pl. "ing", "ban"). |
| horgonyok | StringHashMap(u64) | Kiemelt fontosságú tokenek, amelyeket nyomon követnek a visszakereséshez. |

### Morfológiai listák

A tokenizálót keményen kódolt morfémalistákkal inicializáljuk, amelyek mind az angol, mind a magyar nyelvet támogatják. Ez lehetővé teszi, hogy a tokenizáló hatékonyabban kezelje az összetett magyar szóalakokat (agglutináció), mint a standard BPE.

- Angol előtagok: un, re, pre, dis stb.
- Magyar előtagok: meg, fel, le, be, ki, rá, át stb.
- Magyar utótagok: ban, ben, ból, ből, hoz, hez, stb.

### 3. Adatáramlás és API

### Kódolási logika

Az encode függvény a nyers bájtokról egy core_tensor.Tensor token azonosítókból álló core_tensor.Tensorba való átmenetet irányítja.

Kódolás adatáramlás

### Kulcsfunkciók

### init(allocator, vocab, anchors)

Inicializálja a tokenizálót, feltölti a speciális tokeneket ([PAD], [UNK], [BOS], [EOS]), és regisztrálja a morfológiai listákat.

- Különleges token azonosítók: (0), UNK (1), BOS (2), EOS (3).

### addToken(word)

Új karakterláncot ad hozzá a szótárhoz. Ha a karakterlánc már létezik, akkor a meglévő azonosítót adja vissza. A memória tulajdonjogát úgy kezeli, hogy a karakterláncokat az allocated_strings-ben tárolja.

- Források:  87

### isKnownSpecialTokenStart(text, pos)

A beolvasási fázis során alkalmazott biztonsági ellenőrzés, amely biztosítja, hogy a vezérlőjegyek véletlenül se váljanak részkarakterekre.

### 4. Memóriakezelés és perzisztencia

### Allokációs stratégiák

Az MGT többféle kiosztási mintát támogat a JAIDE egyedi memóriacsomagjával való integráláshoz:

- Arena Allocation: initWithArena a kérés-határolt tokenizáláshoz a következtetési kiszolgálóban.
- Pool allokáció: initWithPool fix méretű tokenek feldolgozásához.
- Buddy Allocation: initWithBuddy dinamikus képzési szókészletekhez.

### Szókincs kitartás

A szókincset bináris formátumban tárolják, ami lehetővé teszi az atomikus betöltést és mentést. Ez biztosítja, hogy a token_to_id hozzárendelések konzisztensek maradnak a különböző képzési futtatások és következtetési telepítések között. A deinit() függvény biztosítja, hogy a tokenizáló élettartama alatt allokált összes karakterláncot felszabadítja az allocated_strings listából.

## SSI: Strukturált szekvenciaindex

A strukturált szekvenciaindex (SSI) egy nagy teljesítményű, vödöralapú fa struktúra, amelyet a JAIDE ökoszisztémán belül a token szekvenciák hatékony visszakeresésére és indexelésére terveztek. Megkönnyíti a Hamming-távolságon alapuló hasonlósági kereséseket, és a csomópontjainak Merkle-szerű hashelésével fenntartja a kriptográfiai integritást.

### Alapadatmodell

Az SSI az adatokat szegmensobjektumokba szervezi, amelyek a csomópontstruktúrák hierarchikus fájában vannak tárolva.

### Szegmens

A szegmens a pontozáshoz és pozicionáláshoz szükséges metaadatokkal társított tokenek különálló sorozatát jelenti.

- Jegyek: <FileRef file-url=" min=20 file-path="src/index/ssi.zig">Hii</FileRef>.
- Pozíció: <FileRef file-url=" min=21 file-path="src/index/ssi.zig">Hii</FileRef>.
- Pontozás: <FileRef file-url=" min=22 file-path="src/index/ssi.zig">Hii</FileRef>.
- Anchor Hash: <FileRef file-url=" min=23 file-path="src/index/ssi.zig">Hii</FileRef>.

### Faszerkezet

Az index egy többszintű fa, ahol minden belső csomópont meghatározott számú vödröt tartalmaz.

- Vödör konfiguráció: Az index 6 bucket_width értéket használ, ami csomópontonként 64 ($2^6$) bucket_countot eredményez <FileRef file-url=" min=15 max=16 file-path="src/index/ssi.zig">Hii</FileRef>.
- Csomópont típusok: <FileRef file-url=" min=61 max=68 file-path="src/index/ssi.zig">Hii</FileRef>.
- Ütközési láncok: A hash ütközések vagy sűrű régiók kezelésére a levélcsomópontok egy CollisionNode összekapcsolt listát használnak <FileRef file-url=" min=56 max=59 file-path="src/index/ssi.zig">Hii</FileRef>.

### SSI-kód egységtérkép

Ez az ábra a logikai indexstruktúra és a Zig implementáció közötti kapcsolatot szemlélteti.

| Logikai entitás | Zig megvalósítás | Szerep |
| --- | --- | --- |
| Index Root | SSI struct | Minden művelet belépési pontja, kezeli az allokátort és a gyökérmutatót <FileRef file-url=" min=8 max=13 file-path="src/index/ssi.zig">Hii</FileRef>. |
| Facsomópont | SSI.Node | Rekurzív struktúra, amely vagy gyermekeket vagy szegmenseket tartalmaz<FileRef file-url=" min=61 max=68 file-path="src/index/ssi.zig">Hii</FileRef>. |
| Data Unit | SSI.Segment | A tényleges indexelt tartalom tokenekkel és metaadatokkal <FileRef file-url=" min=19 max=24 file-path="src/index/ssi.zig">Hii</FileRef>. |
| Overflow | SSI.CollisionNode | Kapcsolódó lista több szegmenshez, amelyek ugyanahhoz a levélhez tartoznak <FileRef file-url=" min=56 max=59 file-path="src/index/ssi.zig">Hii</FileRef>. |

Források: <FileRef file-url=" min=8 max=68 file-path="src/index/ssi.zig">Hii</FileRef>

### Keresés és visszakeresés

Az SSI támogatja a nagy sebességű hasonlósági keresést és a top-K keresést.

### Hamming-távolság hasonlóság

A hasonlóságot a tokenszekvenciák összehasonlításával számítják ki. A retrieveTopK funkció (és a kapcsolódó rangsorolási logika) lehetővé teszi a rendszer számára, hogy a tokenek átfedése és a pontozási metaadatok alapján megtalálja a lekérdezésnek leginkább megfelelő szekvenciákat.

### Hardver-gyorsított keresés

A nagy áteresztőképességű követelmények miatt a keresési logika véges állapotú gépként (FSM) van implementálva Clash-ben (Haskell-alapú RTL), ami lehetővé teszi a bináris fa keresést memória-latencia absztrakcióval.

Főbb hardverkomponensek:

- HashKey64: <FileRef file-url=" min=14 file-path="src/hw/rtl/SSISearch.hs">Hii</FileRef>.
- SearchState: FileRef file-url=" min=38 max=42 file-path="src/hw/rtl/SSISearch.hs">Hii</FileRef>.
- ssiSearchT: Az átmeneti függvény, amely a fa átszelését és a mélységhatár-ellenőrzést kezeli (max. mélység 64) <FileRef file-url=" min=67 max=84 file-path="src/hw/rtl/SSISearch.hs">Hii</FileRef>.

Források: <FileRef file-url=" min=38 max=102 file-path="src/hw/rtl/SSISearch.hs">Hii</FileRef>

### Integritás és karbantartás

### Merkle-szerű Hash integritás

Az SSI minden csomóponthoz gördülő hash-t tart fenn az adatok integritásának biztosítása és a különböző indexállapotok közötti gyors összehasonlítás megkönnyítése érdekében.

- Leaf Hashing: Egy levél hash-ja az elsődleges szegmense és az ütközési láncában lévő összes szegmens fullHash() értékének összege <FileRef file-url=" min=187 max=198 file-path="src/index/ssi.zig">Hii</FileRef>.
- Ágazat-hashelés: Egy ágcsomópont hash-ja az összes gyermeke hash-jának összege <FileRef file-url=" min=200 max=210 file-path="src/index/ssi.zig">Hii</FileRef>.
- Frissítés: A refreshHash függvény frissíti egy csomópont hash-jét a típus alapján <FileRef file-url=" min=212 max=214 file-path="src/index/ssi.zig">Hii</FileRef>.

### Sorozatba rendezés és exportálás

Az SSI támogatja a bináris szerializálást és a tenzorintegrációt:

- Bináris szerializáció: A fa szerkezetének és a szegmensadatoknak a megőrzése mellett az index lemezen is tárolható.
- Tensor exportálás/importálás: A szegmensek exportálhatók Tensor formátumba (kifejezetten 134-es tensor_width értékkel) az RSF neurális csővezeték általi feldolgozáshoz <FileRef file-url=" min=17 file-path="src/index/ssi.zig">Hii</FileRef>.

### Kompakt és egyensúlyi műveletek

A teljesítmény fenntartása érdekében az index növekedése során az SSI a következő műveleteket tartalmazza:

- Kompakt: Az üres csomópontok eltávolítása és a felesleges ütközési láncok ellaposítása.
- Egyensúly: A fa átszervezése annak érdekében, hogy a magasság ne haladja meg a max_height értéket (alapértelmezett 6) és a vödrök kihasználása hatékony legyen <FileRef file-url=" min=11 max=13 file-path="src/index/ssi.zig">Hii</FileRef>.

### Adatáramlás: beszúrás és kivonatolás

A következő sorrend egy új token-sorozat beillesztését írja le az SSI-be.

1.   Hash generálás: hashTokens kiszámítja a bemeneti []u32<FileRef file-url=" min=124 max=131 file-path="src/index/ssi.zig">Hii</FileRef> u64 hash-ját.
2.   Bucket Selection: A bucketIndex a pozíció/hash alsó 6 bitjét használja a <FileRef file-url=" min=142 max=144 file-path="src/index/ssi.zig">Hii</FileRef> útvonal kiválasztásához.
3.   Áthaladás: A fán addig haladunk, amíg egy levelet vagy egy üres vödröt nem találunk.
4.   Levél behelyezése:
- Ha a levél üres, akkor a szegmens <FileRef file-url=" min=234 max=236 file-path="src/index/ssi.zig">Hii</FileRef> kerül tárolásra.
- Ha ütközés történik, egy új CollisionNode kerül hozzáadásra <FileRef file-url=" min=91 max=97 file-path="src/index/ssi.zig">Hii</FileRef>.

5.   Hash-propagáció: a refreshHash rekurzívan hívódik a fán felfelé a szülői csomópontok hash-jának frissítéséhez <FileRef file-url=" min=212 max=214 file-path="src/index/ssi.zig">Hii</FileRef>.

Források: <FileRef file-url=" min=116 max=237 file-path="src/index/ssi.zig">Hii</FileRef>, <FileRef file-url=" min=90 max=102 file-path="src/hw/rtl/SSISearch.hs">Hii</FileRef>

## Ranker

### "Nyitott adattár")

Devin

Utolsó indexálás: 2026. május 10. (

Menü

### Ranker

A Ranker egy nagy teljesítményű szekvencia pontozó és rangsoroló motor a JAIDE rendszeren belül. A tokenszekvenciák relevanciáját és minőségét az n-gram elemzés, a szemantikai hasonlóság és a strukturált szekvenciaindex (SSI) strukturális metaadatainak kombinálásával értékeli. Támogatja az olyan fejlett funkciókat, mint a streaming rangsorolás a valós idejű feldolgozáshoz, a párhuzamos pontozás szálak segítségével, valamint a súlyok kalibrálása gradiens süllyedésen keresztül a keresési pontosság optimalizálása érdekében.

### Core Ranking Logika

A rangsoroló egy sokoldalú pontozási függvényt valósít meg, amely egyensúlyt teremt a helyi n-gramm egyezések és a globális szekvencia-tulajdonságok között. Az elsődleges pontozási belépési pont a scoreSequence, amely egy 0.0 és 1.0 közötti normalizált értéket ad

### Pontszámítási összetevők

1.   N-gram pontozás: A rendszer a szekvenciákat különböző hosszúságú n-grammokra bontja (num_ngrams-ig). Minden n-grammot feldarabolunk és megkeressük az SSI-ben
2.   Bomló súlyok: Az N-grammok hozzájárulásait a hosszuk alapján súlyozzuk harmonikus csökkenéssel ($1/n$), ahol a hosszabb n-grammok specifikusabban, de ritkábban járulnak hozzá a teljes pontszámhoz
3.   Token sokszínűség: Az egyedi tokenek és az összes token arányaként számítva, büntetve az ismétlődő vagy degenerált szekvenciákat
4.   Horgonyzás közelsége: Értékeli a tokenek és az SSI-n belül létrehozott horgonyok közötti térbeli kapcsolatot

### Matematikai modell

A nyers pontszám a következőképpen kerül kiszámításra: $$S_{nyers} = S_{ngram} + (W_{div} \cdot S_{div}) + (W_{prox} \cdot S_{prox})$$$ Az eredményt ezután a MAX_RAW_SCORE (alapértelmezett 100.0) értékhez szorítjuk és normalizáljuk

### Sorozat rangsorolás Flow

A következő ábra a nyers tokenektől a végső rangsorolásig tartó adatáramlást szemlélteti a Ranker és az SSI entitások segítségével.

Szekvencia pontozási csővezeték

### Hasonlósági mérőszámok

A Ranker számos módszert kínál a szekvenciák összehasonlítására a lekérdezésekkel vagy más szekvenciákkal, megkönnyítve ezzel a keresési feladatokat.

### Jaccard hasonlóság (Exact & MinHash)

A rangsoroló a Jaccard-hasonlóság két változatát valósítja meg:

- Pontos Jaccard: AutoHashMap-ot használ a tokenhalmazok metszéspontjának kiszámításához
- MinHash (LSH): Locality Sensitive Hashing: A nagy dimenziós teljesítmény érdekében Locality Sensitive Hashinget használ. A HASH_SEED_MULTIPLIER_A/B-ból származó magok felhasználásával num_hash_funkciókat generál a hasonlóság állandó idő alatt történő becsléséhez

### Koszinusz hasonlóság a Tensoron keresztül

A szemantikai összehasonlításhoz a Ranker a Tensor rendszert használja. A tokeneloszlásokat vagy beágyazásokat tenzorokká alakítja, és a nagyságrendek szerint normalizált pontszorzatot végez

### BitSet hasonlóság

A rendkívül gyors, alacsony pontosságú szűréshez a rangsoroló a BitSet típust használja a bitenkénti AND/OR műveletek elvégzésére az átfedések közelítésére

### Teljesítmény és méretezés

### Párhuzamos pontozás

A Ranker támogatja a nagy mennyiségű szekvencia egyidejű pontozását. Egy szálkészletet használ a scoreSequence-hívásoknak a rendelkezésre álló CPU-magok közötti elosztására, jelentősen csökkentve a késleltetési időt a nagy SSI-indexekből történő top-K lekérdezéshez.

### Streaming Ranker

A streamingRank implementáció gördülő ablakos megközelítést használ

- STREAMING_BUFFER_SIZE: 1024 token.
- STREAMING_WINDOW_SIZE: 512 token. Ahogy új tokenek érkeznek, a rangsoroló fokozatosan frissíti a pontszámokat anélkül, hogy a teljes puffert újra feldolgozná.

### Top-K Heap

A legrelevánsabb eredmények hatékony fenntartása érdekében a rangsoroló egy topKHeap-et használ. Ez a struktúra biztosítja, hogy csak a legmagasabb pontszámú szekvenciák maradjanak meg a nagyméretű keresések során, fenntartva az $O(N \log K)$ komplexitást.

Ranker párhuzamos végrehajtási modell

### Súly kalibrálás

A rangsoroló nem statikus; támogatja a súlyoptimalizálást gradiens süllyedés útján. Ez lehetővé teszi a rendszer számára, hogy az optimális ngram_weights és komponens-súlyokat (Diversity, Proximity) az alapigazság szerinti relevancia-visszacsatolás alapján megtanulja.

### Kalibrálási folyamat

1.   Gradiens számítás: A rendszer kiszámítja a rangsorolási hiba részleges deriváltját az egyes súlyok függvényében.
2.   Frissítési szabály: A súlyok frissítése a LEARNING_RATE (alapértelmezett 0.01) használatával történik
3.   Korlátozások: A súlyok általában úgy vannak korlátozva, hogy pozitívak maradjanak, és a pontszámok stabilitásának biztosítása érdekében normalizálva vannak.

### Import/Export

A rangsoroló konfigurációk, beleértve a kalibrált súlyokat és LSH paramétereket, sorba rendezhetők és deserializálhatók. Ez lehetővé teszi a képzett rangsoroló modellek különböző JAIDE példányokban vagy az InferenceServerben történő telepítését.

Elutasíthatod

Frissítse ezt a wikit

Ez a wiki nemrégiben frissült. Kérjük, várjon 7 napot az újbóli frissítéshez.

### Ezen az oldalon

## Következtetési kiszolgáló API

A JAIDE Inference Server egy nagy teljesítményű HTTP/1.1 szolgáltatás, amelyet valós idejű modellkiszolgálásra terveztek. Robusztus interfészt biztosít a következtetés elvégzéséhez a Reversible Scatter Flow (RSF) architektúrát használó, az MGT tokenizálóval és az SSI visszakeresési indexszel integrált, robusztus interfészt. A kiszolgáló szálbiztos párhuzamosságra épül, kérésenkénti arénaelosztást és többrétegű biztonságot használ, beleértve a Bearer token hitelesítést és a csúszóablakos sebességkorlátozást.

### Kiszolgáló architektúra áttekintése

A szerver az InferenceServer struktúrában van elhelyezve, amely a TCP listener, a szálkészlet és a mögöttes AI komponensek (RSF, SSI, Ranker és MGT) életciklusát kezeli.

Következtetési kiszolgáló komponens kapcsolat:

### Fő végpontok

A kiszolgáló két elsődleges HTTP/1.1 végpontot tesz közzé:

| Végpont | Módszer | Leírás |
| --- | --- | --- |
| /v1/health | GET | Visszaadja a kiszolgáló állapotát, üzemidejét és a modell betöltési állapotát. |
| /v1/inference | POST | Elfogadja a JSON hasznos terhelést a szövegfeldolgozáshoz és a beágyazás generálásához. |

### Egészségügyi ellenőrzések

A /v1/health végpont egy HealthResponse-t ad vissza, amely metaadatokat tartalmaz a futó példányról, beleértve a verziót és azt, hogy az RSF modell sikeresen inicializálódott-e az importModel segítségével

### Következtetési kérelmek

A /v1/inference végpont fogyaszt egy InferenceRequestet Ez egy összetett csővezetéket indít el, amely magában foglalja a tokenizálást, az RSF-rétegeken való továbbhaladást, a relációs kontextus NSIR-modulációját és egy SSI-indexfrissítést a memóriaperzisztencia fenntartása érdekében.

### Biztonság és erőforrás-gazdálkodás

A kiszolgáló több védelmi réteget alkalmaz a stabilitás és az engedélyezett hozzáférés biztosítása érdekében:

- Bearer Token hitelesítés: Ha a require_api_key engedélyezve van a ServerConfigban, a kiszolgáló érvényesíti az Authorization: Bearer <kulcs> fejlécet a JAIDE_API_KEY környezeti változóval.
- IP-nkénti sebességkorlátozás: A RateLimiter egy csúszó ablakot (alapértelmezett 60 másodperc) használ, amelyet a RequestLog StringHashMap-jában tárolnak a visszaélő ügyfelek nyomon követésére és blokkolására.
- Arena-Per-Request memória: A memória fragmentálódásának megelőzése és a nagy átviteli sebesség biztosítása érdekében minden egyes kérés feldolgozása egy dedikált ArenaAllocator segítségével történik. Ez lehetővé teszi a tömeges kiosztás megszüntetését a válasz elküldését követően.
- Szálbiztos párhuzamosság: Poolt használ a bejövő kapcsolatok kezelésére, a megosztott modellsúlyok és az SSI-index védelmét pedig RwLock és Mutex primitívek biztosítják.

A hitelesítési folyamattal és a belső allokátor használatával kapcsolatos részleteket lásd a

### Kérelem-feldolgozási folyamat

Az alábbi ábra a következtetési kérés logikai folyamatát az egyes szakaszokért felelős kódegységekhez rendeli hozzá.

Természetes nyelv és kód közötti entitás leképezés:

### Kiszolgáló belépési pont

A szerver elsődleges belépési pontja az inference_server_main.zig. Ez a modul kezeli a parancssori argumentumok elemzését (pl. --port, --model, --require-api-key) és inicializálja a ServerConfig

A main függvény instanciálja az InferenceServer-t, és meghívja a server.start() parancsot, amely megköti a TCP-csatlakozót, és elindítja a figyelési kört.

A különböző fő belépési pontok és CLI-beállítások részleteiért lásd a

## Kérés életciklusa és biztonsága

A JAIDE Inference Server egy nagy teljesítményű HTTP/1.1 interfész, amelyet úgy terveztek, hogy szigorú biztonsági korlátok és determinisztikus memóriahasználat mellett kezelje az egyidejű következtetési kéréseket. Ez az oldal részletesen bemutatja egy kérés útját a kezdeti TCP kézfogástól a végső JSON-válasz szerializálásáig.

### A kérelemáramlás áttekintése

A következtetési kiszolgáló többszálú rendszerként működik, ahol minden bejövő kapcsolatot egy külön szál kezel, egy aréna-kérésenkénti allokációs stratégiát alkalmazva a memória fragmentálódásának megelőzése és az egyes tranzakciók utáni teljes tisztítás biztosítása érdekében.

### Kérés csővezeték diagram

A következő ábra a hálózati rétegtől a biztonsági szűrőkön keresztül az alapvető neurális és relációs feldolgozóegységekbe való átmenetet szemlélteti.

Kérelemfeldolgozási architektúra

### 1. Biztonság és hozzáférés-ellenőrzés

### Hitelesítés

A kiszolgáló a hitelesítést egy Bearer token mechanizmuson keresztül hajtja végre. Ha a ServerConfig.require_api_key engedélyezve van, a kiszolgáló lekérdezi a JAIDE_API_KEY-t a környezetből. Minden kérésnek tartalmaznia kell egy Authorization: Bearer <kulcs> fejlécet. A megfelelő kulcs megadásának elmulasztása azonnali 401 Unauthorized választ eredményez.

### Rátakorlátozás

A sebességkorlátozás a RateLimiter struktúra által kezelt csúszóablakos algoritmus segítségével valósul meg.

- Tárolás: StringHashMap(RequestLog), ahol a kulcsok IP-címek
- Mechanizmus: ArrayList(i64) időbélyegzőkből
- Érvényesítés: A checkAndRecord meghívásakor a szerver az window_seconds (alapértelmezett 60s) értéknél régebbi időbélyegeket törli, és ellenőrzi, hogy a fennmaradó szám meghaladja-e a max_requests értéket

### 2. Memóriakezelés: A kérés aréna

A nagy áteresztőképesség biztosítása és a memóriaszivárgás elkerülése érdekében a kiszolgáló minden egyes kéréshez egy std.heap.ArenaAllocator-t használ.

1.   Kiosztás: A kapcsolat elfogadásakor egy új Arena inicializálódik.
2.   Használat: Az összes köztes objektum - beleértve az InferenceRequest struktúrát, a tokenizált puffereket és az InferenceResponse JSON stringet - ezen az arénán belül kerül kiosztásra.
3.   Felosztás: Miután a válasz elküldésre került az ügyfélnek, az arena.deinit() meghívásra kerül, amely egyetlen $O(1)$ művelettel visszaszerzi a kérés életciklusa során felhasznált összes memóriát.

### 3. A következtetési csővezeték

Miután egy kérés hitelesítése és az InferenceRequest.fromJson segítségével történő elemzése megtörtént, a kérés belép az alapvető feldolgozási csővezetékbe.

### 1. lépés: Tokenizálás (MGT)

A nyers bemeneti szöveget átadjuk az MGT-nek (Morpheme-Guided Tokenizer). Ez morfológiai dekompozíciót és BPE visszafejtést végez, hogy a szöveget tokenazonosítók sorozatává alakítsa.

- Funkció: Kódolás(allokátor, szöveg)

### 2. lépés: RSF előre passzolás

A tokeneket tenzorrá alakítjuk, és átvezetjük a Reversible Scatter Flow (RSF) rétegeken. A hagyományos transzformátorokkal ellentétben az RSF bijektív csatolási rétegeket használ, amelyek megőrzik az információ sűrűségét.

- Funkció: RSFLayer.forwardInPlace(input_tensor, súlyok)

### 3. lépés: NSIR és SSI kölcsönhatás

Az így kapott látens beágyazásokat az NSIR (Self-Similar Relational Graph) és az SSI (Structured Sequence Index) lekérdezésére használjuk.

- NSIR moduláció: Az NSIR gráf belső kvantumállapota modulálja az RSF kimeneteket, hogy relációs kontextust adjon be.
- SSI visszakeresés: A kiszolgáló Hamming-távolságú hasonlósági keresést végez, hogy megtalálja a releváns szegmenseket a történelmi adatbázisból.
- Funkció: K(query_tensor, k)

### 4. lépés: Rangsorolás

A rangsoroló az SSI-ből kinyert jelölteket az n-gram pontozás, a horgonyok közelsége és a Jaccard-hasonlóság segítségével értékeli, hogy a tokenek végső sorrendjét létrehozza.

- Funkció: StreamingRank(candidates, window_size)

### 4. Válasz szerializáció

A végső kimenet egy InferenceResponse struktúrába van kódolva.

| Mező | Típus | Leírás |
| --- | --- | --- |
| tokens | []u32 | A generált token azonosítók sorozata. |
| embeddings | ?[]f32 | Opcionális látens vektor (ha a return_embeddings true). |
| processing_time_ms | f64 | Teljes késleltetés a kérés beérkezésétől a válasz generálásáig. |

A toJson metódus manuálisan építi fel a JSON hasznos terhelést egy std.ArrayList(u8) és egy író segítségével, hogy minimalizálja a kiosztási terheket és biztosítsa a lebegőpontos beágyazások pontos formázását

### Kód Entitás leképezés

A következő ábra a kérés életciklusának logikai szakaszait a kódbázisban található konkrét végrehajtási fájlokhoz és struktúrákhoz rendeli.

Rendszer-kód egységtérkép

## Fő belépési pontok

A JAIDE rendszer több belépési pontot kínál különböző végrehajtási környezetekhez, a helyi CLI-képzéstől és következtetéstől kezdve a nagy teljesítményű, elosztott GPU-képzésen át a gyártásra kész HTTP-kiszolgálókig. Ezek a belépési pontok koordinálják a különböző alrendszereket, beleértve az RSF processzort, az MGT tokenizálót és az NSIR kvantum-relációs gráfot.

### CLI belépési pont (main.zig)

az src/main.zig a CPU-alapú műveletek elsődleges interfésze, beleértve a modellképzést, az interaktív REPL következtetést és a szintetikus adatok generálását. Kezeli a globális MainConfig-et, amely meghatározza a rendszer alapértelmezett architekturális hiperparamétereit.

### Kulcsfeladatok

- Konfigurációkezelés: Alapértelmezett konstansok meghatározása a beágyazási méretek, RSF-rétegek és optimalizáló beállítások számára
- Végrehajtási módok: Többféle üzemmódot támogat, beleértve a tréninget, az interaktív (REPL), a szintetikus generálást és a tesztelést
- Komponensek összehangolása: Az alapvető csővezeték inicializálása: MGT (tokenizáló), RSF (processzor), SFD (optimalizáló) és SSI (index)

### A végrehajtás részletei: Inicializálási folyamat

Az src/main.zig fájlban található main függvény jellemzően elemzi a parancssori argumentumokat, hogy feltöltsön egy Config struktúrát, majd a kiválasztott módtól függően inicializálja a szükséges modulokat.

| Mode | Primary Action | Key Code Entity |
| --- | --- | --- |
| train | A képzési ciklus végrehajtása az SFD optimalizáló használatával | sfd_mod.SFD | sfd_mod.SFD |
| interaktív | REPL indítása a valós idejű szövegfeldolgozáshoz | mgt_mod.MGT |
| szintetikus | PRNG segítségével generál képzési adatokat | types.PRNG |

### Következtetési kiszolgáló (inference_server_main.zig)

az src/inference_server_main.zig a JAIDE webszolgáltatásként való telepítésének belépési pontja. Az InferenceServer-t csomagolja, hogy HTTP/1.1 interfészt biztosítson a távoli következtetési kérésekhez.

### Adatáramlás: Kiszolgáló indítása

A kiszolgáló belépési pontja egy szabványos inicializálási mintát követ, és a hallgatási ciklusba való belépés előtt beállítja a hálózati paramétereket.

1.   Memóriaelosztás: GeneralPurposeAllocator-t használ a hosszú élettartamú szerverállapothoz
2.   Konfiguráció: A ServerConfig beállítása a port (8080), az állomás (0.0.0.0.0) és a kötegméret (32) alapértelmezett értékeivel
3.   Argumentumelemzés: CLI-zászlókkal, mint a --port, --model és --require-api-key, felülbírálja az alapértelmezetteket
4.   Életciklus: Az InferenceServer inicializálása és a .start() hívása a kérelmek kezelésének megkezdéséhez

### GPU és elosztott belépési pontok

A JAIDE speciális belépési pontokat használ a hardverrel gyorsított képzéshez. Ezeket a belépési pontokat úgy tervezték, hogy NVIDIA hardverrel (H100/B200) működjenek, és Futhark által generált CUDA kerneleket használjanak.

### Egy GPU-s képzés (main_gpu.zig)

az src/main_gpu.zig egyetlen H100 GPU-t céloz meg. A GPUCoordinator-t 1 world_size értékkel inicializálja, és DistributedTrainerFuthark-ot használ az f16 pontosságú kernelek futtatásához

### Több GPU-s elosztott képzés

Két elsődleges multi-GPU belépési pont van:

1.   Hibrid kvantum-klasszikus (main_distributed.zig):

- Több GPU koordinálása az NCCL használatával
- Integrálható az IBM Quantum backendekkel, ha az IBM_QUANTUM_API_KEY jelen van
- A GPUCoordinator segítségével szinkronizálja a rangok közötti gradienseket

2.   Futhark-gyorsított (main_distributed_futhark.zig):

- Fókuszál a tiszta GPU teljesítményre a Futhark kernelek használatával
- NVLinkre optimalizált f16 pontossággal
- Fájl alapú NCCL ID csere mechanizmust használ a rangsor szinkronizálásához

### Belépési pont logikai leképezése

A következő ábra azt szemlélteti, hogy a különböző belépési pontok hogyan kapcsolódnak az egyes hardverekhez és képzési háttérrendszerekhez.

## Belépési pont a backend leképezéshez

Források:    58

### Elosztott szinkronizálási folyamat

Az elosztott belépési pontok közös mintát használnak a több csomópontú kommunikáció NCCL-en keresztüli inicializálásához. Ez biztosítja, hogy a GPU összes sora szinkronizálva legyen a képzési ciklus megkezdése előtt.

## Elosztott inicializálási sorozat

### A belépési pont jellemzőinek összehasonlítása

| Feature | main.zig | main_gpu.zig | main_distributed.zig | main_distributed_futhark.zig | main_distributed_futhark.zig |
| --- | --- | --- | --- | --- |
| Elsődleges eszköz | CPU | 1x H100 | 8x B200 | 8x B200 | 8x B200 |
| Precíziós | f32 | f16 | f32/f16 | f16 | f16 |
| Backend | Native Zig | Futhark/CUDA | Native/NCCL | Futhark/NCCL | Futhark/NCCL |
| Quantum támogatás | Nem | Nem | Nem | Igen (IBM) | Nem | Nem |
| Ellenőrzőpontok | model_io | saveCheckpoint | loadCheckpoint | saveCheckpoint |

Források: 17 22 31 127

## NSIR: önhasonló relációs gráf

Az NSIR (Non-Scalar Information Retrieval) ökoszisztéma a JAIDE kvantum-relációs tudásrétegét képviseli. A sima vektorbeágyazásokon túl egy nagydimenziós, önhasonló gráfszerkezetbe lép át, ahol a csomópontok fogalmakat, az élek kapcsolatokat, a kvantumállapotok pedig bizonytalanságot és több kontextusú relevanciát jelentenek.

A rendszer lényege a SelfSimilarRelationalGraph, amely a klasszikus gráfelméletet kvantumszimulációval integrálja, hogy lehetővé tegye a nemlineáris gondolkodást és a fraktális tudásszervezést.

### Rendszer áttekintése: Természetes nyelv az entitások kódolásához

Az alábbi ábra azt szemlélteti, hogy az NSIR ökoszisztéma magas szintű architektúrális koncepciói hogyan illeszkednek a src/core_relational/ könyvtárban található konkrét Zig struktúrákhoz és modulokhoz.

NSIR koncepció feltérképezése

### NSIR Core Graph

Az alapvető adatszerkezet a SelfSimilarRelationalGraph. A szabványos gráfokkal ellentétben az NSIR-ben minden csomópont tartalmaz egy Qubitot, amely lehetővé teszi a rendszer számára, hogy valószínűségi információs állapotokat reprezentáljon. Az élek az EdgeQuality szerint vannak kategorizálva, a szuperpozíciótól (feloldatlan kapcsolatok) a fraktálig (önhasonló rekurzív struktúrák).

A legfontosabb képességek a következők:

- Kvantumkapu műveletek: A hadamardGate, pauliXGate és phaseGate alkalmazása csomóponti állapotokra
- Topológia integritás: A gráf szerkezeti érvényességének biztosítása érdekében Merkle-stílusú hashing Sha256-on keresztül
- Mátrix export: ExportAdjacencyMatrix segítségével a gráftopológia átalakítása Tensor formátumba a klasszikus neurális feldolgozáshoz.

A részletekért lásd

### Reasoning Orchestrator & ESSO Optimizer

Az NSIR-ben a következtetést úgy kezeljük, mint egy energiaminimalizálási problémát a gráfban. A ReasoningOrchestrator kezeli a különböző Gondolkodási szintek szakaszait (helyi, globális és meta-érvelés) Az ESSO-t (Entangled Stochastic Symmetry Optimizer) használja a minták felismerésére és a gráf fraktáldimenzióinak újbóli kiegyensúlyozására.

A hangszerelés magában foglalja:

- ChaosCoreKernel: Aszinkron végrehajtási ciklusok kezelése gráffrissítésekhez
- Szimmetria észlelés: SymmetryGroup és SymmetryPattern használata ismétlődő relációs struktúrák azonosítására

A részletekért lásd

### CREV Pipeline & tudásfelvétel

A CREV (Contextual Relational Extraction and Validation) csővezeték az elsődleges adatbeviteli motor. A nyers adatokat RelationalTriplet struktúrákká alakítja át (Subject-Relation-Object)

A csővezeték elvégzi:

1.   Kivonás: Az entitások és kapcsolatok kinyerése szövegből vagy metaadatokból.
2.   Érvényesítés: Az új adatok és a meglévő gráf ismeretek közötti konfliktusok feloldása.
3.   Indexelés: Az eredmények tárolása a KnowledgeGraphIndexben a gyors visszakeresés érdekében

A részletekért lásd

### Kvantum logika és feladatadapter

A szimulált kvantumlogika és a tényleges hardver összekapcsolása érdekében a QuantumTaskAdapter azonosítja a kvantumgyorsításra alkalmas részgráfokat. OpenQASM utasításokat generál, és az IBMQuantumClient segítségével továbbítja azokat az IBM Quantumhoz hasonló szolgáltatókhoz

Kvantum végrehajtási folyamat

A részletekért lásd

### Biztonság, védelem és ellenőrzött következtetés

Az NSIR ökoszisztéma tartalmaz egy szigorú verifikációs réteget. formal_verification.zig egy TheoremProver-t biztosít a gráftranszformációk validálásához, míg security_proofs.zig a tudásbázis kriptográfiai integritását biztosítja

A VerifiedInferenceEngine ezeket a bizonyítékokat a zk_verification (Zero-Knowledge) segítségével kombinálja, hogy a gráf következtetési folyamat kimenetei biztonságosak és matematikailag megalapozottak legyenek

A részletekért lásd

## NSIR Core Graph

A Neural-Symbolic Information Retrieval (NSIR) Core Graph, amelyet SelfSimilarRelationalGraph néven valósítottak meg, egy kvantum-klasszikus hibrid adatszerkezet, amelyet úgy terveztek, hogy a tudást a kvantumállapotokkal rendelkező csomópontok és élek dinamikus hálózataként ábrázolja. Ez biztosítja a relációs következtetés alaprétegét, lehetővé téve az adategységek közötti valószínűségi összefonódást és a fraktál alapú topológiai szerveződést.

### Rendszerarchitektúra áttekintése

Az NSIR Core Graph áthidalja a "természetes nyelvi teret" (ahol olyan fogalmak léteznek, mint a "Subject-Relation-Object") és a "Code Entity Space"-t azáltal, hogy ezeket a fogalmakat olyan speciális Zig-struktúrákra képezi le, mint a Node, Edge és Qubit.

### Kapcsolattérképezés: Nyelv a kódhoz

A következő ábra azt szemlélteti, hogy a magas szintű relációs fogalmak hogyan kerülnek az nsir_core.zig implementációban alkalmazásra.

NSIR koncepció feltérképezése

### Adatszerkezetek

### 1. Node

Egy csomópont egy különálló entitást vagy fogalmat képvisel a gráfon belül. Minden csomópont egy Qubit segítségével fenntartja a saját helyi kvantumállapotát.

- id: Egyedi azonosítója a csomópontnak.
- adatok: Az entitáshoz tartozó nyers bájt hasznos adat.
- qubit: A csomópont valószínűségi állapotát reprezentáló qubit struktúra.
- fázisban: Interferencia számításokban használt skalárérték.
- metaadatok: StringHashMap tetszőleges kulcs-érték attribútumokhoz.

### 2. Edge és EdgeQuality

Az élek a csomópontok közötti kapcsolatokat határozzák meg. A klasszikus gráfokkal ellentétben az NSIR élek "minőséggel" rendelkeznek, amely meghatározza fizikai-számítási viselkedésüket.

- EdgeQuality Enum:
- szuperpozíció: A kapcsolat több potenciális állapotban létezik.
- összefonódva: Az egyik csomópont állapotának változása hatással van a másikra.
- összefüggő: stabil, szinkronizált kapcsolat.
- összeomlott: Összeomlott: Egy mért/rögzített kapcsolat.
- fraktál: Egy önhasonló rekurzív kapcsolat.

### 3. Qubit

A Qubit struktúra egy szabványos kétállapotú kvantumrendszert valósít meg komplex számokkal (Complex(f64)).

- normalizeInPlace(): Biztosítja, hogy a valószínűségi amplitúdók $\alpha$ és $\beta$ megfeleljenek a $|\alpha|^2 + |\beta|^2 = 1$ feltételnek.
- prob0() / prob1(): Kiszámítja annak valószínűségét, hogy a csomópont a mérés után 0 vagy 1 állapotba esik.

### Kvantumműveletek és logika

A SelfSimilarRelationalGraph módszereket biztosít a csomópontok kvantumállapotainak manipulálására, a kapuműveletek és a több csomópontos kölcsönhatások szimulálására.

### Kapu megvalósítások

A gráf támogatja a csomóponti qubitekre alkalmazott szabványos kvantumkapukat:

- Hadamard (H): Egy csomópontot szuperpozíciós állapotba helyez.
- Pauli-X/Y/Z: Forgások a Bloch-gömb tengelyei körül.
- Fáziskapu: A $|1\rangle$ állapot fázisának beállítása.

### Összefonódás és mérés

- entangleNodes(id1, id2): A két csomópont közötti EdgeQuality-t összefonódottra állítja, és korrelálja a quantum_correlation komplex értékeit.
- measure(node_id): A hullámfüggvény összeomlását váltja ki. A csomópont Qubitje az aktuális valószínűségeloszlása (prob0/prob1) alapján vagy initBasis0() vagy initBasis1() állapotba kényszerül.

### Gráf topológia és integritás

### Merkle-stílusú topológia Hash

A gráf egy SHA-256 Merkle-stílusú hashing mechanizmus segítségével tartja fenn az integritást és a verziókezelést.

- topológia hash: Az összes csomópont és él determinisztikus sorrendben történő iterálásával (azonosító szerint rendezve).
- Az egyes csomópontok hash-ját (beleértve az adatokat és a qubit-állapotot) kombináljuk a kapcsolódó élek hash-jával, hogy létrehozzuk a teljes gráf állapotát reprezentáló gyökér hash-ját.

### Memória életciklus

A grafikon hibrid memóriastratégiát alkalmaz:

1.   Kiutaló: A hosszú élettartamú csomópontok és élek tárolására egy szabványos Zig allokátor szolgál.
2.   deinitNodeMap: A csomópontok azonosítóinak, metaadatainak és magának a csomópont-térképnek a rekurzív felszabadítására szolgáló speciális segédprogram.
3.   clearNodeMapRetainingCapacity: A gráf visszaállítása során az újrakiosztások minimalizálása érdekében.

### Export és integráció

Az NSIR Core Graph az igazság forrásaként szolgál a szélesebb JAIDE ökoszisztéma számára, és exportot biztosít a neurális feldolgozáshoz.

| Funkció | Leírás |
| --- | --- |
| exportNodeEmbeddings | A csomóponti adatokat és kvantumfázisokat egy core_tensor.Tensorba konvertálja az RSF réteg bemenetéhez. |
| exportAdjacencyMatrix | Egy súlyozott szomszédsági mátrixot generál, ahol a súlyokat az EdgeQuality és a quantum_correlation modulálja. |

### Adatáramlás: A tudás bevitele a grafikon állapotába

Ez a diagram azt követi nyomon, hogyan áramlanak a nyers adatok a CREV csővezetékből a SelfSimilarRelationalGraphba.

NSIR adatáramlás

## Reasoning Orchestrator & ESSO Optimizer

A Reasoning Orchestrator és az Entangled Stochastic Symmetry Optimizer (ESSO) alkotja a JAIDE rendszer hierarchikus intelligenciamotorját. Ez az alrendszer felelős a SelfSimilarRelationalGraph (NSIR) energiaállapotának minimalizálásáért a strukturális szimmetriák azonosításával, a fraktálok kiegyensúlyozásával és a többszintű érvelési ciklusok végrehajtásával.

### 1. Reasoning Orchestrator

A ReasoningOrchestrator kezeli az érvelési folyamat életciklusát a különböző absztrakciós rétegeken keresztül. Koordinál a ChaosCoreKernel az alacsony szintű gráfmutációkhoz és az ESSO a magas szintű szimmetriaoptimalizáláshoz.

### Hierarchikus gondolati szintek

Az érvelés három különböző Gondolkodási szint kategóriára osztható:

- Helyi: A közvetlen csomópontok szomszédságára és a peremek minőségére összpontosít
- Globális: Az általános topológiával és a nagyléptékű összekapcsolhatósággal foglalkozik
- Meta: Az érvelési folyamat önreferenciális optimalizálását végzi

### Adatáramlás: Érvelési fázis Végrehajtás

Az orchestrator az érvelést diszkrét ReasoningPhase blokkokban hajtja végre. Minden egyes fázis nyomon követi az energia konvergenciáját és a minta felfedezését.

| Komponens | Funkció | Leírás |
| --- | --- | --- |
| ReasoningPhase | hasConverged | Ellenőrzi, hogy a relatív energiaváltozás a konvergencia-küszöbérték alatt van-e |
| ReasoningOrchestrator | perturbLocalNodes | A csomópontok helyzetét véletlenszerűen megzavarja, hogy elkerülje a helyi minimumokat |
| ReasoningOrchestrator | updateLocalEdges | Az élsúlyok finomítása a helyi kapcsolati metrikák alapján |
| ReasoningOrchestrator | runChaosCycle | ChaosCoreKernel ciklus indítása a strukturális entrópia injektálásához |

### 2. ESSO (Entangled Stochastic Symmetry Optimizer)

Az EntangledStochasticSymmetryOptimizer az alapvető optimalizáló motor. "Összefonódott" sztochasztikus kereséseket használ a gráf teljes energiáját minimalizáló szimmetriaminták (rotációs, reflexiós, transzlációs) megtalálására.

### Szimmetria csoportok

Az ESSO többféle SymmetryGroup típust azonosít és alkalmaz a gráfra:

- reflexió: Tükrözés egy paraméterek által meghatározott tengelyen[3]
- rotation_90/180/270: Diszkrét ortogonális forgatások
- custom_rotation: Tetszőleges szögelfordulások
- fordítás: Lineáris eltolódások a relációs térben

### Optimalizálási csővezeték

1.   Inicializálás: A SymmetryPattern jelöltek populációjának létrehozása.
2.   Perturb: Alkalmazza a stochasticPerturb paraméterekre (origó, skála, szög)
3.   Értékeljük: Számítsa ki az OptimizationState energiáját az ObjectiveFunction segítségével
4.   Belebonyolódni: Állapotok szinkronizálása minták között a szerkezeti felfedezések megosztása érdekében.

### 3. Káosz mag és fraktál kiegyensúlyozás

A ChaosCoreKernel az orchestrator "anyagcseréje". Kezeli a MemoryBlock-állapotokat, és az FNDS (Fractal Node Data System) segítségével kezeli a FractalTree újrakiegyenlítését.

### Káosz magállapotok

A gráfon belüli csomópontok és memóriaszegmensek a MemoryBlockState életcikluson keresztül haladnak:

- kiosztva: Aktív adatok a grafikonon.
- összefonódva: Kvantum-relációs élekkel összekapcsolt adatok
- vándorlás: A fraktál kiegyensúlyozás során áthelyezett adatok

### Fraktál újrakiegyenlítő logika

A rendszer a FractalTree műveletekkel tartja fenn a strukturális integritást:

- updateAverageTreeDepth: O(log N) hozzáférés biztosítása érdekében újraszámítja a hierarchikus mélységet
- computeSignature: SHA-256 segítségével egyedi fractal_signature-t generál a szerkezeti változások felismerésére

### 4. Építészeti diagramok

### Érvelés Orchestrációs áramlás

Ez a diagram a magas szintű logikát konkrét kódegységekhez és funkciókhoz rendeli hozzá.

### ESSO állapotátmenet és szimmetria alkalmazás

Ez az ábra azt mutatja, hogy az optimalizáló hogyan hidalja át az absztrakt szimmetriacsoportokat a SelfSimilarRelationalGraph (NSIR) csomópontokhoz.

### 5. Konvergencia és statisztika

Az OrchestratorStatistics struktúra valós idejű telemetriát biztosít az érvelő motor teljesítményéről.

| Statisztika | Forrásmező | Leírás |
| --- | --- | --- |
| Legjobb energia | best_energy_achieved | Az összes fázisban talált legalacsonyabb energiaállapot |
| Konvergenciaidő | average_convergence_time | A konvergencia küszöbérték eléréséhez szükséges idő futó átlaga |
| Patterns | patterns_discovered | A rögzített egyedi szimmetriaminták száma |
| Fázisszámlálás | local/global/meta_phases | Az egyes hierarchikus szinteken elköltött erőfeszítések megoszlása |

## CREV Pipeline & tudásfelvétel

A Contextual Relational Extraction and Validation (CREV) csővezeték az elsődleges kapu a strukturálatlan és félig strukturált adatok NSIR-be (Self-Similar Relational Graph) történő beviteléhez. A nyers bemeneti adatokat (szöveg, CSV vagy metaadatok) ellenőrzött RelationalTriplet struktúrákká alakítja át, a ChaosCoreKernel segítségével anomália-pontozást alkalmaz, és a globális gráf állapotának frissítése előtt feloldja a tudáskonfliktusokat.

### 1. Pipeline architektúra és adatáramlás

A CREV csővezeték szakaszos állapotgépként működik, a nyers adatokból az indexált tudás felé haladva. Az egyes szakaszokat az ExtractionStage enum határozza meg

1.   Tokenizálás: Kezdeti szövegfeldolgozás az MGT rendszer segítségével.
2.   Triplet kivonás: Tárgy-Reláció-Tárgy minták azonosítása.
3.   Érvényesítés: Anomália pontozás és bizalmi súlyozás.
4.   Integráció: SelfSimilarRelationalGraph csomópontokkal való összevonás.
5.   Indexelés: A KnowledgeGraphIndex frissítése a gyors visszakeresés érdekében.

### Pipeline adatáramlás (Természetes nyelvből kódolt entitásokba)

A következő ábra azt szemlélteti, hogy a külső adatok hogyan alakulnak át belső nsir_core és crev_pipeline entitásokká.

### 2. Relációs triplett struktúra

A CREV csővezeték alapvető tudásegysége a RelationalTriplet. A szabványos RDF-tripletekkel ellentétben ezek valószínűségi bizalmi pontszámokat és kriptográfiai identitáshasheket tartalmaznak.

### Főbb összetevők

- Identitás-kaszálás: Minden triplettnek van egy forrás_kasza, amelyet a hashTripletIdentity segítségével generálnak, így biztosítva, hogy ugyanaz az alany-reláció-tárgy kombináció nyomon követhető legyen a különböző kivonási időpontokban.
- Bizalom és szorítás: A bizalom mezőt automatikusan 0,0 és 1,0 közé szorítja a clamp01 segítségével
- Metaadatok tárolása: U8) lehetővé teszi a csővezeték számára, hogy a forrás eredetét (pl. fájl offsets, kép metaadatok) a tripletthez csatolja

### 3. Validálás és anomáliák pontozása

Az érvényesítést a ValidationEngine kezeli, amely a ChaosCoreKernelbe integrálódik, hogy meghatározza, ha az új információ ellentmond a gráf aktuális "entrópiájának".

### Anomália pontozási logika

A csővezeték a bejövő RelationalTriplet és a KnowledgeGraphIndex összehasonlításával kiszámítja az anomália pontszámot. Ha egy triplet olyan kapcsolatot állít, amely jelentősen eltér a csomópontok megállapított SignalState-jétől, akkor manuális felülvizsgálatra vagy alacsonyabb súlyozású integrációra kerül megjelölésre.

| Metrika | Kódegység | Cél |
| --- | --- | --- |
| Jaccard Dissimilarity | SurpriseMetrics.jaccard_dissimilarity | A tartalom átfedését méri a meglévő memóriablokkokkal. |
| Időbeli újdonság | SurpriseMetrics.temporal_novelty | Megállapítja, hogy az információ mennyire "új" a TEMPORAL_NOVELTY_WINDOW_NS-hez képest. |
| Kombinált meglepetés | SurpriseMetrics.combined_surprise | A jaccard, a hash távolság és az időbeli újdonság átlaga. |

### 4. ChaosCore & StreamBuffer integráció

A nagy áteresztőképességű bevitel kezeléséhez a csővezeték egy StreamBuffer-t használ a bejövő triplák kötegelésére, mielőtt a ChaosCoreKernel feldolgozza őket.

### ChaosCoreKernel kölcsönhatás

A ChaosCoreKernel "energiaminimalizálást" végez a gráfon. Amikor a CREV csővezeték egy új triplát injektál:

1.   A StreamBuffer felhalmozza a triplákat.
2.   A ChaosCoreKernel elindít egy ciklust a helyi csomópontok megzavarására
3.   Ha az új triplett csökkenti a globális energiát (javítja a gráf konzisztenciáját), akkor a SelfSimilarRelationalGraph-ba keményedik.

### 5. Időbeli grafikon átalakítása

Az érvényesítést követően a hármasok a TemporalGraph-on belül NodeVersion és EdgeVersion objektumokká alakulnak át. Ez lehetővé teszi a rendszer számára, hogy a tudás fejlődésének előzményeit megőrizze.

### Verziókezelési mechanizmus

- NodeVersion: Kvantumállapotát (amplitúdó és fázis) tárolja egy adott időbélyegnél
- EdgeVersion: EdgeQuality: Egy adott időpontban rögzíti a kapcsolat EdgeQuality-jét és súlyát
- Jelterjedés: Az új ismeretek jelet indítanak a SignalPropagationEngine-on keresztül, amely frissíti a kapcsolt csomópontok fázisát és amplitúdóját a triplett bizalmassága alapján

## Kvantum logika és feladatadapter

A JAIDE rendszer kvantumszámítási képességeket integrál az NSIR (Self-Similar Relational Graph) relációs következtetéseinek fokozására. Ez az integráció egy nagy hűségű helyi szimulátor (RelationalQuantumLogic) és egy hardveres útválasztó réteg (QuantumTaskAdapter) között oszlik meg, amely az OpenQASM generáción keresztül kapcsolódik az IBM Quantum hardveréhez.

### Relációs kvantumlogika (helyi szimulátor)

A RelationalQuantumLogic osztály kifejezetten relációs adatokra tervezett kvantumáramkörök helyi, nagy pontosságú szimulációját biztosítja. Olyan QuantumState objektumokat kezel, amelyek a tudásgráf csomópontok valószínűségi és összefonódott természetét reprezentálják.

### Kvantum állapot reprezentáció

A rendszer minden qubitjét egy QuantumState struktúra reprezentálja, amely a $|0\rangle$ és $|1\rangle$ alapállapotok komplex amplitúdóit tárolja

- Amplitúdók: Két Complex(f64) érték, amelyek az állapotvektort reprezentálják
- Összefonódási fok: A kvantumkorreláció erősségét jelzi más csomópontokkal
- Normalizálás: A normalize() függvény biztosítja, hogy a teljes valószínűség nagysága egyenlő legyen 1.0-val

### Támogatott logikai kapuk

A rendszer támogatja a szabványos kvantumkapukat és a speciális relációs operátorokat

- Szabványos: FÁZIS, CNOT, TOFFOLI.
- Kapcsolati: RELÁCIÓS_ÉS, RELÁCIÓS_VAGY, RELÁCIÓS_NEM, RELÁCIÓS_XOR.
- Fraktál: FRACTAL_TRANSFORM, amelyet több skálájú állapotkeveréshez használnak.

### Végrehajtási folyamat: Természetes nyelvből kódba

A következő ábra a magas szintű kvantumfogalmakat a quantum_logic.zig és vpu.zig fájlokban található konkrét megvalósításukhoz rendeli.

Kvantum-klasszikus entitás leképezés

### Quantum Task adapter

A QuantumTaskAdapter hídként működik a SelfSimilarRelationalGraph és a végrehajtási háttértár között. Azonosítja azokat az algráfokat, amelyeknek előnyös lenne a kvantumfeldolgozás, és továbbítja őket a helyi szimulátorhoz vagy az IBM Quantum hardverhez

### Algráf azonosítása

Az adapter két elsődleges metrika alapján keresi a QuantumSubgraph-jelölteket az NSIR-gráfban

1.   Összefonódási küszöbérték: A teljes kvantumkorrelációnak az élek között meg kell haladnia egy meghatározott határértéket (alapértelmezett 0,5)
2.   Fraktális dimenzió: A részgráf átlagos fraktáldimenziójának nagyobbnak kell lennie, mint 1,5

### Hardver integráció és útválasztás

Ha a use_real_backend engedélyezve van, az adapter az IBMQuantumClientet használja a feladatok elküldéséhez

- IBMQuantumClient: Kezeli a HTTP/1.1 kommunikációt az IBM Cloud API-val. OpenQASM payloadokon keresztül kezeli a feladatok benyújtását, és a getJobResult segítségével lekérdezi az eredményeket
- Backend specifikációk: A különböző IBM architektúrákra (Heron, Eagle, Falcon, Osprey, Condor) vonatkozó hardveres korlátozások (T1/T2 idők, kapuhibák) a quantum_hardware.zig fájlban vannak tárolva

Feladatvégzés adatáramlás

### VPU (Vektorfeldolgozó egység)

A VPU biztosítja a kvantumállapot-műveletek SIMD-gyorsított gerincét. A Zig @Vector típusát használja a kvantum amplitúdókon végzett párhuzamos műveletek elvégzésére

### SimdVector képességek

A SimdVector(T, N) általános struktúra nagy teljesítményű matematikai műveleteket valósít meg:

- Aritmetika: add, sub, mul, divChecked
- Lineáris algebra: pontszorzat, nagyságrend és normalizálás
- Hardveres gyorsítás: Fma-t (Fused Multiply-Add) használ, ahol a CPU támogatja

### Vektor típusok

A rendszer többféle vektorszélességet és pontosságot támogat az átviteli teljesítmény és a pontosság egyensúlyának megteremtése érdekében

| Típus | Sávok | Kijelölés | Használat |
| --- | --- | --- | --- |
| f32x8 | 8 | 32 bájt | Nagy teljesítményű szimuláció |
| f64x4 | 4 | 32 bájt | Nagy pontosságú állapotfrissítések |
| i32x8 | 8 | 32 bájt | Diszkrét relációs logika |

### Hardver kötések és kalibrálás

A quantum_hardware.zig fájl statikus specifikációkat tartalmaz az IBM Quantum háttértárakhoz, amelyeket az adapter a zaj szimulálásához vagy a legmegfelelőbb fizikai eszköz kiválasztásához használ.

- Kalibrációs adatok: IBMBackendCalibrationData követi a T1/T2 relaxációs időket és a kapuhibák arányát
- Eszközhatárok: A QuantumConfig olyan korlátozásokat határoz meg, mint a MAX_QUBITS_SIMULATION (20) és a HARDWARE_MAX_SHOTS (100,000)
- Backend specifikációk: Az IBMDocumentedBackendSpecs a hibák átlag- és szórásértékeit adja meg, lehetővé téve a QuantumTaskAdapter számára a hardverzaj reális modellezését a helyi szimuláció során

## Biztonság, védelem és ellenőrzött következtetés

A JAIDE rendszer többszintű biztonsági és védelmi architektúrát tartalmaz, amelynek célja, hogy biztosítsa a relációs tudásgráfok integritását, a képzési adatok titkosságát és a következtetési eredmények matematikai helyességét. Ez az alrendszer futásidejű biztonsági ellenőrzéseket, kriptográfiai bizonyításokat, formális tételbizonyítást és ZK-ellenőrzött következtetést foglal magában.

### Rendszerarchitektúra áttekintése

A biztonsági architektúra három fő területre oszlik:

1.   Futásidő-biztonság: Alacsony szintű memória- és aritmetikai hitelesítés.
2.   Kriptográfiai biztonság: Homomorfikus titkosítással és a biztonsági irányelvek érvényesítésével történő adathalmaz-eltitkosítás.
3.   Ellenőrzött következtetés: A modell végrehajtásának matematikai bizonyítása TheoremProver és ZK-SNARK segítségével.

### Kód Entitás leképezés

A következő ábra a magas szintű biztonsági fogalmakat a core_relational modulon belül az azokat megvalósító konkrét kódegységekhez rendeli.

Biztonsági és védelmi egységtérkép

### Futásidejű biztonság (safety.zig)

A safety.zig modul olyan primitíveket biztosít, amelyekkel megelőzhetők a szoftverek gyakori sebezhetőségi osztályai, például az egész számok túlcsordulása és a nullmutató dereferenciák, amelyek kritikusak egy nagy teljesítményű Zig-környezetben.

### Kulcsfontosságú primitívek

- Integer Safety: a safeIntCast határérték-ellenőrzést végez az előjeles és előjel nélküli típusok között, és SafetyError.IntegerOverflow vagy IntegerUnderflow értéket ad vissza, ha az átvitel érvénytelen
- Mutatók ellenőrzése: a safePtrCast biztosítja, hogy a mutatók nem nullák és megfelelnek a céltípus igazítási követelményeinek
- Biztonságos törlés: a secureZeroBytes és a secureZeroSlice illékony írást használ, hogy biztosítsa, hogy az érzékeny adatok (például a kulcsok) valóban törlődjenek a memóriából, és ne a fordító optimalizálja őket
- Biztonságos RNG: A SecureRng struktúra az std.crypto.random struktúrát használja, hogy kriptográfiailag biztonságos véletlenszámokat biztosítson a perturbációkhoz és a kulcsgeneráláshoz

### Biztonsági bizonyítékok és irányelvek (security_proofs.zig)

A rendszer olyan klasszikus modelleken alapuló formális biztonsági szabályzatot valósít meg, mint a Bell-LaPadula (bizalmasság) és a Biba (sértetlenség).

### Biztonsági szintek és jogok

A rendszer a biztonsági és integritási szintek rácsszerkezetét határozza meg:

- SecurityLevel: (0) és TOP_SECRET (4) között
- IntegrityLevel: (0) és KERNEL (3) között
- AccessRight: Bitmaszk, beleértve a READ, WRITE, EXECUTE, DELETE és ADMIN jelszavakat is

### Szabályzat végrehajtása

A SecurityError enum olyan jogsértéseket sorol fel, mint a NonInterferenceViolation, BellLaPadulaViolation és BibaViolation. Ezeket a gráfműveletek során használják annak biztosítására, hogy az információ ne áramoljon a magas biztonságú csomópontokból az alacsony biztonságú csomópontokba.

### Adathalmaz elfedése és homomorfikus titkosítás

Az érzékeny képzési adatok védelmére a JAIDE a Paillier-kriptoszisztémát használja, amely lehetővé teszi a homomorf összeadást a titkosított értékeken.

### Paillier végrehajtás

A PaillierKeyPair az n, g, lambda, és mu

- Titkosítás: Az i64-es nyílt szöveg kódolása és kombinálása egy r véletlenszerű tényezővel az u512-es rejtjelezett szöveg előállításához
- Homomorf összeadás: add(c1, c2) kiszámítja $(c1 c2) \pmod{n^2}$, ami a tiszta szövegek összegére dekódolja a kódot
- Skaláris szorzás: multiplyScalar(c, scalar) moduláris exponenciálással szoroz meg egy titkosított értéket egy plaintext konstanssal

### Formális verifikáció és tételbizonyító

A formal_verification.zig-ben található TheoremProver egy logikai motor, amelyet gráfinvariánsok ellenőrzésére használnak.

### Logikai motor

A bizonyító több ProofRule típust támogat, beleértve a MODUS_PONENS, INDUCTION és CONTRADICTION típusokat:

- KAPCSOLATOSSÁG: A gráf elérhetősége.
- EGYÜTTMŰKÖDÉS: Kvantumállapot érvényessége.
- MEMORY_SAFETY: Határok és allokáció érvényessége.

### Ellenőrzött következtetési motor

A VerifiedInferenceEngine a modell végrehajtása során ZK-SNARK bizonyításokat és homomorfikus titkosítást végez.

Következtetés-ellenőrzés folyamata

### Hardver és futásidejű integráció

### R-GPU (Relációs GPU)

Az r_gpu.zig modul a ProcessingCore egységekből álló Network-on-Chip (NoC) hálózatot kezeli

- Power Gating: A magok lehetnek üresjárati, feldolgozási vagy power_gated állapotban az energiafogyasztás optimalizálása érdekében
- Üzenetátadás: A magok NoCMessage-en keresztül kommunikálnak olyan típusokkal, mint a weight_update és a graph_sync

### Z-Runtime

A z_runtime.zig modul biztosítja a relációs műveletek végrehajtási környezetét. Minden művelethez (pl. entangle_variables, fractal_transform) egy ExecutionHistoryEntry-t tart fenn, lehetővé téve a gráf állapotainak teljes ellenőrizhetőségét és visszaállítását

### C API

A c_api.zig stabil interfészt biztosít külső nyelvek számára az NSIR gráffal való interakcióhoz. Olyan szabványos hibakódokat definiál, mint a JAIDE_ERROR_NULL_POINTER és a JAIDE_ERROR_INTEGRITY_VIOLATION, hogy biztosítsa a biztonsági határok fenntartását az FFI-ben

## Hardveres gyorsítás

A JAIDE hardvergyorsító rétege többszintű megközelítést biztosít a nagy teljesítményű számításokhoz, amely magában foglalja a magas szintű GPU-kerneleket, az egyéni hardverek alacsony szintű RTL-szintézisét és a több GPU-s képzés elosztott szervezését. Ezt a réteget úgy tervezték, hogy a számításigényes feladatokat - például a Reversible Scatter Flow (RSF) transzformációkat, a Structured Sequence Index (SSI) keresést és a kvantumállapot-szimulációkat - a CPU-ról a speciális hardverre terelje.

A rendszer az AccelContext és a FutharkContext struktúrákon keresztül kapcsolódik a hardverhez, amelyek a GPU-erőforrások életciklusát és a szinkronizációt kezelik.

### Rendszerarchitektúra áttekintése

A következő ábra a magas szintű Zig alkalmazáskód, a Futhark GPU-kernelek és a Clash által generált hardverkomponensek közötti kapcsolatot szemlélteti.

Hardveres gyorsító egység leképezése

### Futhark GPU magok

A JAIDE GPU-gyorsítás magja Futhark nyelven íródott, amely egy funkcionális adatpárhuzamos nyelv, amely nagymértékben optimalizált OpenCL vagy CUDA kernelekké fordítható. Ezek a kernelek az RSF-csatorna és az SSI-keresési rendszer matematikai nehéz munkájának nagy részét végzik.

A Futharkban megvalósított legfontosabb funkciók a következők:

- RSF műveletek: rsf_forward_layer és rsf_backward_layer, amelyek a bijektív csatolás és a szórás matematikáját valósítják meg.
- Keresési gyorsítás: ssi_find_nearest és topk gyors hasonlósági keresés nagy szekvenciaindexekben.
- Optimalizálás: fisher_diagonal_update és spectral_natural_gradient az SFD optimalizálóhoz.

A kernel implementációkkal és a Futhark manifesztummal kapcsolatos részletekért lásd

### RTL hardver szintézis (Clash/Haskell)

Az extrém alacsony késleltetést vagy FPGA/ASIC célpontokon történő telepítést igénylő forgatókönyvek esetében a JAIDE tartalmaz Clash (egy Haskell-RTL fordító) nyelven írt hardverleírásokat. Ez az alréteg a strukturált szekvenciaindex (SSI) keresési logikájára és rangsorolására összpontosít.

Az RTL-összetevők a következők:

- SSISearch FSM: Véges állapotú gép bináris fák hardveres átjárására, a SearchState és a NodeAddr32 típusok felhasználásával a memóriakésleltetés absztrahálására.
- MemoryArbiter: Kezeli a nagy sávszélességű memóriához való többportos hozzáférést a párhuzamos rangsoroló magok számára.

A hardveres FSM-ekkel és a szintézis csővezetékkel kapcsolatos részletekért lásd

### Elosztott képzés

A hatalmas adathalmazokra történő képzés skálázása érdekében a JAIDE egy olyan elosztott képzési protokollt valósít meg, amely több GPU-t szinkronizál a csomópontok között. Ez a rendszer az NCCL-t (NVIDIA Collective Communications Library) használja a hatékony gradiens szinkronizáláshoz.

Elosztott koordinációs áramlás

Az DistributedTrainer klasszikus és hibrid kvantum-klasszikus munkaterhelést egyaránt kezel, biztosítva, hogy az összesReduce művelet konzisztens modellsúlyokat tartson fenn a fürtön belül. A felhőszervezést a modal_gpu.zig kezeli a dinamikus allokációhoz.

Az NCCL integráció és a több GPU-s skálázás részleteiért lásd

### Gyorsítási interfész összefoglaló

Az accel_interface.zig-ben található interfészréteg biztosítja a kapcsolatot a Zig memóriakezelése és a GPU között.

| Komponens | Felelősség | Kódhivatkozás |
| --- | --- | --- |
| FutharkContext | Kontextus inicializálása és szinkronizálása | | |
| PinnedMemory | CUDA host-pinned memória kiosztása a gyors DMA-hoz | | |
| FutharkArray2DF16 | 2D félpontosságú GPU tömbök csomagolása | | |
| gpu_enabled | A hardveres tehermentesítésre vonatkozó fordítási idejű jelző | | |

## Futhark GPU magok

A Futhark gyorsítócsomag nagy teljesítményű GPU-kerneleket biztosít a JAIDE rendszer számára, amelyek lefedik a neurális hálózati műveleteket, a gráffeldolgozást és a kvantumszimulációkat. Ezek a kernelek C-kötéseken keresztül integrálódnak a Zig kódbázisba, és olyan nehéz számítási feladatok kezelésére szolgálnak, amelyek CPU-n nem lennének hatékonyak.

### Építészet és integráció

Az integrációs réteg kezeli a Futhark-kontextus életciklusát és az adatok mozgását a gazdamemória és a GPU-eszköz memóriája között.

### Futhark kontextus kezelése

A FutharkContext struktúra kezeli a GPU-környezet inicializálását és szinkronizálását. Beállítja az alapértelmezett csoportméreteket, a csempe méreteket és az eszköz azonosítókat

| Funkció | Cél | Forrás |
| --- | --- | --- |
| init() | Új Futhark konfigurációt és kontextust rendel hozzá, a default_group_size értékét 256-ra, a default_tile_size értékét pedig 32-re állítja. | |
| sync() | Kényszeríti a szinkronizálást a host és a GPU-eszköz között. | |
| deinit() | Felszabadítja a mögöttes Futhark-kontextust. | |

### Memória átjárhatóság

Az adatok átvitele speciális tömbfelhúzók (FutharkArray1DF16, FutharkArray2DF16) segítségével történik, amelyek a Futhark átláthatatlan tömbtípusaihoz kapcsolódnak A teljesítmény optimalizálása érdekében a JAIDE a CUDA kötéseken keresztül pined memóriát használ az átviteli késleltetés csökkentése érdekében

### Adatáramlás: Zig to Futhark Kernelek

A következő ábra azt szemlélteti, hogy a Zig struktúrákat a kernel futtatásához Futhark-kompatibilis típusokká alakítják.

Maghívási csővezeték

### Neurális hálózati magok (RSF & SFD)

A JAIDE neurális gyorsításának lényege a Reversible Scatter Flow (RSF) kernelekben és a Stochastic Fisher Diagonal (SFD) optimalizáló frissítésekben rejlik.

### RSF csővezeték

Az RSF magok bijektív csatolási rétegeket valósítanak meg. Az rsf_forward kernel a bemeneti sorokat két félre osztja, az első felére (a második alapján) méretarány-transzformációt, majd a második felére transzformációt alkalmaz

- Előre passz: Y1 = x1 exp(s(x2)) és y2 = x2 + t(y1)
- Visszafelé passz: Hatékonyan kiszámítja a súlyok (súlyok_s, súlyok_t) és az előítéletek (s_bias, t_bias) gradienseit az előremenő menet közbenső értékeinek felhasználásával
- Többrétegű: rsf_forward_multi több RSF réteget kapcsol össze, permutációkat alkalmazva az egyes áramlások között

### SFD optimalizáló frissítések

Az sfd_update_half és sfd_update_bias kernelek a súlyfrissítési logikát a momentummal valósítják meg

- Fisher Information: fisher_diagonal_update fenntartja a Fisher Information Matrix diagonálisának futó becslését a négyzetes gradiensek és a lecsengési tényező felhasználásával
- Természetes gradiens: a spectral_natural_gradient a Fisher-diagonálisra csillapítást alkalmaz a természetes gradiens frissítésének kiszámításához

### Visszakeresés és SSI magok

A strukturált szekvenciaindex (SSI) és a rangsorolási műveletek gyorsítottak a nagyméretű hasonlósági keresések kezeléséhez.

### SSI Hashing és rangsorolás

- Szegmens pontozás: A score_segments kernel kiszámítja a lekérdezés hash-jával való megfelelési bónuszokat a szegmensek hash-jára
- Top-K kiválasztás: A topk kernel radix rendezéssel azonosítja a legmagasabb pontszámokat és a hozzájuk tartozó indexeket egy nagy tételből

### Rendszer leképezése: Visszakeresési logika

Források:  67

### RGPU grafikus és fraktálfeldolgozás

A FractalLPU (Logic Processing Unit) kezeli a grafikus műveletek végrehajtását a GPU-n, a terheléselosztás optimalizálása érdekében fraktáldimenziós konfigurációkat használva.

### Fraktál partícionálás

A FractalTile struktúra a gráf memóriaterületének rekurzív felosztását jelenti

- Alosztály: A csempék a Hausdorff-dimenzió és a box_counting_levels alapján gyermekekre vannak osztva
- Terheléskiegyenlítés: A balanceLoad függvény a szűk keresztmetszetek elkerülése érdekében újraosztja a függő_műveleteket a ComputeUnit példányok között egy lapkán belül

### Fixpontos végrehajtás

Az executeFixedPoint függvény a grafikon adatait fixpontos aritmetikával dolgozza fel, a bemeneteket a csempe koherenciafaktorával skálázva

### Manifeszt és külső függőségek

A futhark.pkg manifeszt a kernel implementációjához szükséges külső Futhark könyvtárakat követi, különösen a diku-dk/sorts csomagot, amelyet a Top-K kernelekben a radix rendezéshez használnak

### Kulcsfontosságú magbejegyzések (C-kötések)

A futhark_bindings.zig fájl a lefordított Futhark kerneleket teszi elérhetővé a Zig számára.

| Belépési pont | Cél |
| --- | --- |
| futhark_entry_matmul | Standard 2D mátrix szorzás. |
| futhark_entry_rsf_forward | Gyorsított RSF réteg előrehaladás. |
| futhark_entry_training_step | Kombinált előre, veszteség, visszalépés és frissítési lépés. |
| futhark_entry_rank_segments | SSI szegmens rangsorolás a lekérdezés hash-jai alapján. |

## RTL hardver szintézis (Clash/Haskell)

Ez a szakasz a JAIDE rendszer regiszter-transzfer szintű (RTL) hardverkomponenseit ismerteti, amelyeket a Clash funkcionális hardverleíró nyelv segítségével valósítottunk meg. Ezek a komponensek a strukturált szekvenciaindex (SSI) keresési logikájának, a rangsoroló algoritmusoknak és a memória arbitrációnak a hardverrel gyorsított megvalósítását biztosítják a nagy teljesítményű keresési feladatokhoz.

### SSISearch FSM

Az SSISearch modul egy hardveres véges állapotú gépet (FSM) valósít meg a strukturált szekvenciaindex (SSI) bináris fa szerkezetének bejárására. A memóriakésleltetést a facsomópontok lekérdezéséhez egy kérés-válasz kézváltás segítségével absztrahálja.

### Adatszerkezetek

A keresési logika több kulcstípusra támaszkodik a 64 bites kulcsok és a 32 bites címtartomány kezeléséhez:

- HashKey64: A keresési kulcsot jelképező 64 bites egész szám
- NodeAddr32: 32 bites címmutató a memóriahelyek számára
- TreeNode: A nodeKey, leftChild, rightChild és egy érvényességi bitet tartalmazó csomópontot képvisel az SSI-fában

### Keresés állapotgép

Az FSM-et a SearchState típus és az ssiSearchT átmeneti függvény határozza meg

| Állapot | Leírás |
| --- | --- |
| Idle | SearchRequestre vár. |
| Letöltés | TreeNode-adatok várakozása a memóriából egy adott NodeAddr32 számára. |
| Összehasonlítás | A searchKey és a nodeKey összehasonlítása a következő ág meghatározásához. |

A keresési folyamatot a MaxSearchDepthConfig korlátozza, amely 64-re van beállítva, hogy megakadályozza a végtelen ciklusokat a rosszul formált fa struktúrákban

### Adatáramlás: SSI keresés

A következő ábra a Haskell entitásokat a keresési logikai folyamathoz rendeli:

SSI keresési logika folyamata

### RankerCore Hardveres rangsoroló

A RankerCore modul egy szinkron rangsoroló csővezetéket biztosít, amely a szegmensek végső pontszámát az alappontszámok és a pozícióalapú torzítások alapján számítja ki.

### Pontozási logika

A rangsoroló egy pozíció-előfeszítést alkalmaz, hogy a szegmenseket a szekvenciában elfoglalt helyük alapján büntesse vagy jutalmazza.

- Position Bias: A positionBiasScale / (segmentPos + 1) értékkel számítva, a safeDiv segédprogrammal a nullával való osztás elkerülése érdekében
- Végeredmény: Az alappontszám és a számított torzítás összege

### Állami nyomon követés

A RankerState követi a lastQuery hash-t. Ha egy új RankRequest megegyezik az előző lekérdezéssel, akkor az stateCounter növekszik, gyakorlatilag követve az aktuális eredmény rangját az eredményhalmazon belül

### Adatáramlás: Ranker Pipeline

RankerCore feldolgozás

### MemoryArbiter

A MemoryArbiter kezeli a több portos hozzáférést egy megosztott memóriaforráshoz, lehetővé téve, hogy legfeljebb 4 ügyfél (NumClients) memóriaigénylést adjon ki

### Választottbírósági politika

Az arbiter egy fix prioritású sémát használ (a findIndex isJust-on keresztül) a memóriabuszhoz való hozzáférés biztosításához, amikor az ArbIdle állapotban van Amint egy ügyfélnek hozzáférést biztosítanak, az arbiter az ArbServing állapotba lép a ServiceCycles által meghatározott fix időtartamra (4 ciklus)

### Komponens interfészek

- MemRequest: Tartalmazza a reqAddr (32 bites), a reqData (64 bites), a reqWrite jelzőt és a reqClient ID-t
- MemResponse: Visszairányítja a respData-t a kérést kezdeményező respClienthez
- Szűrés: A válaszok szűrése úgy történik, hogy a filterResp függvényen keresztül csak a kérő ügyfél kapja meg az adott MemResponse-t

### Logikai diagram

Memory Arbiter architektúra

### Szintézis és integráció

Minden modult a Clash fordítóprogrammal szabványos RTL (Verilog/VHDL) szintézisre terveztek. A topEntity wrappereket használják az FPGA vagy ASIC eszközláncokba való integráláshoz a Clock, Reset és Enable jelek exponálásához

## Elosztott képzés

A JAIDE rendszer egy robusztus, több GPU-ra elosztott képzési keretrendszert valósít meg, amelyet klasszikus és hibrid kvantum-klasszikus munkaterhelésre egyaránt terveztek. Ez az alrendszer az NVIDIA kollektív kommunikációs könyvtárát (NCCL) használja a nagy teljesítményű gradiens szinkronizáláshoz és a Modal felhő infrastruktúrát a dinamikus GPU-kiosztáshoz.

### GPU koordináció és NCCL kötések

A JAIDE-ban az elosztott képzés alapja a GPUCoordinator, amely kezeli az eszközök életciklusát, a memória kiosztását és a kollektív műveleteket. A hardverrel az nccl_bindings.zig fájlon keresztül lép kapcsolatba, amely Zig interfészt biztosít a mögöttes C-alapú NCCL és CUDA API-khoz.

### Kulcsfontosságú összetevők:

- GPUCoordinátor: Kezeli a rangok inicializálását, a CUDA streamek kezelését, és absztrakciókat biztosít az eszközmemória műveletekhez
- NCCL kötések: Olyan alapvető kollektív primitívek, mint az ncclAllReduce, ncclBroadcast és ncclCommInitRank
- Kollektív műveletek: A koordinátor olyan speciális módszereket biztosít, mint az allReduceFloat32 és az allReduceFloat16, hogy az ncclSum redukciós műveletet használó csomópontok között szinkronizálja a gradienseket

### Elosztott inicializálási folyamat

A következő ábra azt szemlélteti, hogyan inicializálja egy oktató csomópont a helyi GPU-környezetét, és hogyan csatlakozik a globális NCCL-kommunikátorhoz.

Csomópont inicializálási sorrend

### Elosztott oktatói architektúrák

A JAIDE két elsődleges elosztott tréner implementációt kínál: egy klasszikus DistributedTrainer és egy Futhark-gyorsított változatot.

### DistributedTrainer (klasszikus)

A DistributedTrainer a distributed_trainer.zig-ben egy teljes tensor-alapú képzési hurkot valósít meg a copy-on-write (COW) szemantika és a referenciaszámlálás támogatásával A modell súlyait egy egyéni Tensor struktúra segítségével kezeli, amely támogatja a többdimenziós alakzatokat és lépéseket

### DistributedTrainerFuthark

A DistributedTrainerFuthark nagy teljesítményű GPU-végrehajtásra van optimalizálva. Az RSFAccelerátort használja a Reversible Scatter Flow (RSF) számítások Futhark kernelekre történő áthelyezésére

Kulcsfontosságú jellemzők:

- Hibrid tokenizáció: MGT (Morpheme-Guided Tokenizer) integrálása a bemeneti szöveg feldolgozásához
- Adatkészlet megosztása: Automatikusan kezeli az adathalmaz rang szerinti felosztását, biztosítva, hogy minden GPU a képzési adatok egyedi részhalmazát dolgozza fel
- Tűzött emlék: PinnedMemory-t használ a hatékony host-eszköz közötti átvitelhez

Adatáramlás: A fogadó és a Futhark gyorsító között

### Felhőinfrastruktúra: GPU-kiosztás: modális GPU-kiosztás

A JAIDE a modal_gpu.zig segítségével integrálódik a Modal felhőplatformba, hogy automatizálja a csúcskategóriás GPU-k (pl. NVIDIA B200/B300) elosztott feladatokhoz való rendelkezésre bocsátását.

- ModalGPUClient: Egy HTTP-alapú ügyfél, amely kezeli a Modal API-hoz intézett telepítési kérelmeket
- Munkahelyi bevetés: A deployTrainingJob függvény sorba rendezi a képzési konfigurációkat (kötegméret, epochák, GPU-szám), és elküldi őket a felhőbe
- Dinamikus üzembe helyezés: Támogatja a GPU-beállítások megadását, alapértelmezés szerint B300 és B200 példányok

### Gradiens szinkronizálás és ellenőrzőpontozás

Elosztott környezetben a gradiens szinkronizáció kritikus fontosságú a modell konvergenciája szempontjából.

### Szinkronizációs mechanizmus

1.   Helyi gradiens számítás: Minden rang a saját helyi kötegén az RSFAccelerator segítségével számítja ki a gradienseket.
2.   All-Reduce: A GPUCoordinator hívja az allReduceFloat32 (vagy f16) parancsot. Ez összesíti a gradienseket az összes rangsorban, és az eredményt újraelosztja
3.   Súlyfrissítés: Az optimalizáló (pl. SFD) az átlagolt gradienseket használja a helyi súlyok frissítésére, így az összes rangsor szinkronban marad.

### Ellenőrzés

A TrainerConfig megadja a checkpoint_version-t Az oktatók felelősek az RSFAccelerator állapotának és az MGT szókincsnek a perzisztens tárolóba történő rendszeres mentéséért, ami lehetővé teszi a hardverhibák vagy a felhőkörnyezetekben az elővásárlás utáni helyreállítást.

| Funkció | Szerep | Forrás |
| --- | --- | --- |
| allReduceFloat32 | Szinkronizálja a 32 bites gradienseket az NCCL segítségével | | |
| broadcastFloat32 | Szinkronizálja a kezdeti súlyokat a gyökér rangsorból | | |
| deployTrainingJob | Felhőalapú GPU-k biztosítása Modal segítségével | | |
| extractDatasetText | JSONL képzési minták elemzése | | |

## Formális ellenőrzés

A JAIDE rendszer egy többnyelvű formális verifikációs csomagot használ a matematikai helyesség, a memóriabiztonság és a szerkezeti integritás biztosítására a Reversible Scatter Flow (RSF) és az Orthogonal Fractal Transform Block (OFTB) komponensek esetében. Ez a csomag a Lean 4, Mizar, Twelf, Bel és ZK-SNARK áramkörökben történő bizonyításokon keresztül hidat képez a magas szintű funkcionális specifikációk és az alacsony szintű megvalósítás részletei között.

### Az ellenőrzési területek áttekintése

Az ellenőrzési stratégia négy elsődleges területre oszlik, amelyek mindegyike a rendszer meghatározott tulajdonságait célozza:

| Domain | Nyelv | Elsődleges fókusz |
| --- | --- | --- |
| Funkcionális helyesség | Lean 4 | Az RSF rétegek bijektivitása, a lebegőpontos interfész axiómák és a szerializációs integritás. |
| Matematikai logika | Mizar | Tenzorkalkulus, Xavier inicializálási korlátok és GPU-kompatibilis predikátumok. |
| Rendszerbiztonság | Twelf | Memóriabiztonság (no-alias), regiszter életciklus-átmenetek és rendszerszintű invariánsok. |
| Zero-Knowledge | Circom | Ellenőrzött következtetési nyomvonalak és biztonságos aggregáció a ZK-SNARK-okon keresztül. |

### A természetes nyelvtől a kód-entitásokig

Az alábbi ábra a magas szintű verifikációs fogalmakat a JAIDE ökoszisztémán belül az általuk validált konkrét kódegységekhez rendeli.

Ellenőrzési leképezés: Logika a kódhoz

### 8.1 Sovány 4 Bizonylatok (RSF és OFTB)

A Lean 4 csomag a legszigorúbb funkcionális specifikációt nyújtja az RSF architektúrához. Meghatározza a FloatInterface axiómákat, és bizonyítja az előremenő és az inverz műveletek matematikai egyenértékűségét.

- RSF specifikáció: Validálja a forwardRowSpec, inverseRowSpec és backwardFromOutputsRowSpec specifikációkat az RSFCoreSpec specifikációval szemben.
- OFTB aritmetika: Fixpontos aritmetikai modellt (FP) alkalmaz a pillangó transzformáció stabilitásának bizonyítására.
- Életciklus: Modellezi a RegistryState és GPUState diszpécseri logikát, hogy biztosítsa az állapotátmenetek érvényességét a modell végrehajtása során.

A részletekért lásd

### 8.2 Mizar és tizenkét bizonyíték

A Mizar és a Twelf a rendszer alapvető strukturális tulajdonságainak és működési szemantikájának ellenőrzésére szolgál.

- Mizar (rsf.miz): A Tensor2D tulajdonságaira és a LayerCore jólformáltságára összpontosít. Tartalmazza a ThForwardInverseIdentity tételt, amely bizonyítja, hogy egy forward pass inverze visszaadja az eredeti bemenetet. Meghatározza továbbá a SerializeRSF-et a bináris formátum ellenőrzésére.
- Tizenkettő (rsf.twealf): A memóriabiztonság típuselméleti bizonyítását biztosítja. Igazolja, hogy a tensor-ref műveletek korlát-ellenőrzöttek, és hogy a nyilvántartás életciklusa (az ls-transition segítségével) fenntartja a trace-monotone tulajdonságot, megakadályozva a használat utáni hibákat az RSF nyilvántartásban.

A részletekért lásd

### 8.3 Bel ellenőrzés és ZK-SNARK bizonyítékok

Az ellenőrzés utolsó rétege a futásidejű biztonsági ellenőrzést és a következtetés kriptográfiai bizonyítását foglalja magában.

- Bel (rsf.bel): Relatív biztonsági képlet-ellenőrzőt hajt végre. Rekurzív ereszkedő kiértékelőt használ a tenzorok split-valid és merge-valid tulajdonságainak ellenőrzésére a csatolási réteg végrehajtása során.
- Circom (ZK-SNARKs): FullInferenceProof áramköröket generál. Ezek lehetővé teszik a bizonyító számára, hogy bizonyítsa, hogy egy adott következtetési nyomvonalat egy érvényes RSFLayerComputation generált anélkül, hogy felfedné a mögöttes modell súlyait, a kötelezettségvállalásokhoz Poseidon hashinget használva.

A részletekért lásd

### Rendszerellenőrzés folyamata

A következő ábra azt mutatja be, hogy a különböző verifikációs nyelvek hogyan lépnek kölcsönhatásba a JAIDE alapkomponensekkel egy tipikus építési vagy verifikációs ciklus során.

JAIDE ellenőrző csővezeték

## Lean 4 Proofs (RSF és OFTB)

Ez az oldal a Reversible Scatter Flow (RSF) és az Orthogonal Fractal Transform Block (OFTB) formális verifikációját részletezi a Lean 4 segítségével. A verifikációs csomag biztosítja a bijektív műveletek matematikai helyességét, a fixpontos aritmetika biztonságát és a rendszer állapotának integritását a komplex GPU/CPU diszpécser műveletek során.

### A hitelesítés hatályának áttekintése

A Lean 4 bizonyítás két fő területre oszlik:

1.   RSF Logic (rsf.lean): Az affin csatolási rétegek ellenőrzése, beleértve az előre/vissza identitásbizonyításokat, a nyilvántartási állapotátmeneteket és a bináris szerializációs formátumot (RSF0)
2.   OFTB Logic (oftb.lean): A pillangó-transzformáció ellenőrzése fixpontos aritmetikával, beleértve a fraktál skálázás biztonsági invarianciáit és az iteratív és funkcionális megvalósítások egyenértékűségét

### Feltérképezés: Természetes nyelvi kódok (RSF)

Az alábbi ábra a magas szintű RSF fogalmakat a Lean 4 ábrázolásukkal kapcsolja össze.

RSF rendszer leképezése

### RSF formális specifikáció

Az RSF-ellenőrzés szigorú interfészt definiál a lebegőpontos műveletekre és a tenzor sorok manipulációjára annak bizonyítására, hogy az inverz lépés pontosan visszanyeri az előre lépés bemenetét.

### FloatInterface és numerikus axiómák

Mivel a Lean 4-et szerkezeti bizonyításokra használják, a numerikus műveletek egy FloatInterfészen keresztül absztrahálódnak. Ez lehetővé teszi, hogy a bizonyítás olyan tulajdonságokat feltételezzen, mint az add_comm vagy a mul_assoc, miközben figyelembe veszi az olyan lehetséges ZigError állapotokat, mint a túlcsordulás vagy a nonFiniteValue

### Nyilvántartás és GPU állapot

A rendszer egy RegistryState segítségével követi a modellkezelők életciklusát.

- Kezelje az életciklust: A fogantyúknak aktívból megsemmisítetté kell válniuk anélkül, hogy kétszeresen szabaddá válnának.
- GPU-diszpécser: A GPUState biztosítja, hogy a műveletek csak akkor kerülnek elküldésre, ha a gpuUnavailable hamis és a verziók megegyeznek

Nyilvántartási állapot átmenet áramlása

### RSF0 Sorozatba rendezés

Az RSF0 formátumot a szerkezeti integritás szempontjából ellenőrzik. Az RSF0_Header specifikáció meghatározza a bűvös számok elrendezését, a verziószámozást és a CRC32 ellenőrző összeg követelményét. A bizonyítás biztosítja, hogy bármely rosszFileFormat vagy checksumMismatch eredményezzen ResultT.err

### OFTB hivatalos specifikáció

Az OFTB ellenőrzése az ortogonális fraktál transzformációs blokkra, különösen a Haar-wavelet pillangókeverésre és annak fixpontos aritmetikában történő megvalósítására összpontosít.

### Fixpontos aritmetika (FP)

A lebegőpontos kerekítés nem-determinizmusának elkerülése érdekében az oftb.lean egy egyedi FP struktúrát implementál, amely Int-et használ $10^8$ skálázási tényezővel

| Állandó | Érték (skálázva) | Cél |
| --- | --- | --- |
| scale | 100000000 | Base for $1.0$ |
| fractalScale | 70710678 | $1/\sqrt{2}$ közelítés |
| halfFractalScale | 35355339 | $1/(2\sqrt{2})$ közelítés |

### Pillangó transzformációs logika

Az oftb_butterfly függvény a keveredési réteg magja. Két értéket vesz fel $(a, b)$ és kiszámítja:

1.   $a' = (a + b) \times \text{fractalScale}$
2.   $b' = (a - b) \times \text{fraktálSkála}$

A b_butterfly_inverse bizonyítása azt mutatja, hogy a transzformáció kétszeri alkalmazása (megfelelő skálázással) visszaadja az eredeti értékeket, fenntartva az RSF-hez szükséges bijektivitást

### Feltérképezés: OFTB végrehajtási nyomkövetés kódra

OFTB Végrehajtás és biztonság

### Kulcsfontosságú bizonyítási tételek

### A sor-specifikációk bijektivitása

Az RSF elsődleges tétele az előrehaladás inverzének és az identitásfüggvénynek az egyenértékűsége.

- forwardRowSpec: $y = x \cdot \exp(s) + t$
- inverseRowSpec: $x = (y - t) \cdot \exp(-s)$ kiszámítása
- Tétel: inverseRowSpec (forwardRowSpec x s t) s t = x.

### Iteratív vs. funkcionális ekvivalencia

Az oftb.lean-ben a pillangó transzformáció rekurzív funkcionális definícióként és iteratív ciklusként (a Zig implementációt utánozva) is implementálva van.

- Tétel: oftb_recursive_eq_iterative. Ez biztosítja, hogy a magas szintű matematikai specifikáció megfeleljen az OFTBState-ban használt alacsony szintű ciklusalapú végrehajtásnak

### Biztonsági invariánsok

A SafetyInvariant struktúra az oftb.lean pályákon:

1.   Értékhatárok: Skála által meghatározott tartományon belül kell maradnia, hogy a köztes pillangó lépések során elkerülhető legyen a túlcsordulás
2.   Memóriabiztonság: A listához való hozzáférés a listGet és listSet segítségével bizonyítottan a vektor hosszához viszonyított korlátokon belül van

## Mizar & Twelf Proofs

Ez a szakasz a Reversible Scatter Flow (RSF) architektúra formális ellenőrzését mutatja be a Mizar és a Twelf bizonyítási rendszerek segítségével. Ezek a bizonyítások megállapítják a bijektív csatolási rétegek matematikai helyességét, a tenzorműveletek memóriabiztonságát és a magas integráltságú mesterséges intelligencia következtetéshez és képzéshez szükséges általános rendszerszintű invariánsokat.

### Mizar specifikáció (rsf.miz)

A Mizar specifikáció szigorú axiomatikus alapot biztosít az RSF alapkomponensei számára. A tenzorok szerkezeti érvényességére, az előre- és inverz transzformációk matematikai tulajdonságaira és az inicializálási rutinokra összpontosít.

### Tensor2D és LayerCore

A specifikáció a Tensor2D struktúrát úgy definiálja, mint egy 2D mátrixot, amely valós számok véges sorozatára van leképezve Egy tenzor akkor tekinthető érvényesnek, ha az adatainak hossza megegyezik a dimenziók szorzatával

A LayerCore struktúra tartalmazza az affin csatolási rétegekben használt skála ($s$) és transzlációs ($t$) függvények súlyait és torzításait

### Kulcsfontosságú predikátumok és funkciók

| Név | Leírás | Forrás |
| --- | --- | --- |
| well-formed | Biztosítja, hogy a dimenziók pozitívak legyenek, a vágási tartományok végesek és határok között vannak ([-20, 20]), a súlymátrixok pedig négyzet alakúak legyenek. | |
| InitLayerCore | Meghatározza a súlyok Xavier-inicializálását, biztosítva, hogy a variancia a fan-in/fan-out összeggel legyen skálázva. | |
| ForwardInPlace | Megadja a $y = x \cdot \exp(s) + t$ transzformációt a bemenet egy partíciójára. | |
| InverseInPlace | Megadja a $x = (y - t) \cdot \exp(-s)$ transzformációt, az előrehaladás matematikai inverzét. | |
| ThForwardInverseIdentity | Egy tétel, amely bizonyítja, hogy az InverseInPlace alkalmazása a ForwardInPlace után az eredeti bemenetet adja vissza. | |

### GPU és szerializáció

A specifikáció predikátumokat tartalmaz a GPU-kompatibilitás érdekében, különösen annak ellenőrzését, hogy az értékek F16-konvertálhatók-e, hogy megakadályozza a túlcsordulást az alacsony pontosságú diszpécser során A SerializeRSF függvény meghatározza a bináris formátum elrendezését, beleértve a SAVE_VERSION (jelenleg 4-es verzió) és a CRC32 integritás-ellenőrzéseket

### Tizenkét specifikáció (rsf.twealf)

A Twelf specifikáció az RSF rendszer operációs szemantikájára és típuselméleti biztonságára összpontosít. A memóriabiztonság és az állapotátmenetek modellezésére a HOAS (Higher-Order Abstract Syntax - magasabb rendű absztrakt szintaxis) módszert használja.

### Memóriabiztonság és a nyilvántartás életciklusa

A tizenkettőt arra használják, hogy bizonyítsák, hogy a tenzorreferenciák (tensor-ref) soha nem érik el a korlátokon kívüli memóriát, és hogy a rendszer fenntartja a noalias tulajdonságot, biztosítva, hogy az RSF rétegek in-place műveletei ne rontsák a nem kapcsolódó memóriarégiókat

A kibocsátásiegység-forgalmi jegyzék életciklusát állapotátmeneteken keresztül modellezzük:

1.   ls-transition: Az egyik rendszerállapotból a másikba való érvényes átmenetet határozza meg (pl. inicializálatlan állapotból egy betanított állapotba)
2.   nyomvonal-monoton: Biztosítja, hogy a súlyok verziószámozása csak növekedjen, megakadályozva a régi gradiensek vagy régi modellparaméterek használatát a képzés során

### Teljes rendszer-biztonsági tétel

Az rsf.twealf teljes rendszer-biztonsági tétele szolgál a legfelső szintű bizonyításként. Az mcore-wf (a többmagos végrehajtási állapot jólformáltsága) és a rendszerinvariáns kombinációjával garantálja, hogy ha a rendszer biztonságos állapotban indul, akkor az előremenő vagy inverz műveletek bármely sorozata biztonságos állapotot eredményez

### Természetes nyelv és kód közötti leképezés: Verifikációs tér

A következő ábra a formális ellenőrzés fogalmait a Zig és a Futhark kódbázisban található implementációs entitásokhoz rendeli.

Ellenőrzés a kódhoz Entitás leképezés

### Adatáramlás és változatlan életciklus

A következő ábra azt szemlélteti, hogy a Mizarban és a Twelfben definiált invarianciák hogyan maradnak fenn egy RSF réteg művelet életciklusa során.

RSF invariáns életciklus

### Legfontosabb biztonsági mechanizmusok

- Ellenőrzött aritmetika: A Mizar definiálja a checkedMul és checkedAdd túlcsordulási predikátumokat annak biztosítására, hogy a tenzor indexelési számítások ne tekeredjenek körbe
- Bijektivitás összekapcsolása: A tizenkét csatolás-előre/vissza kapcsolat biztosítja, hogy minden előre irányuló transzformációhoz létezik pontos inverz, ami kritikus fontosságú az SFD optimalizálóban használt O(1) memóriás visszaterjedés szempontjából
- Rendszerinvariánsok: A rendszerinvariáns bizonyítás biztosítja, hogy az NSIR gráf teljes energiája korlátos marad az érvelési ciklusok során, megakadályozva a ReasoningOrchestrator divergenciáját

## Bel ellenőrzés és ZK-SNARK bizonyítékok

Ez a szakasz részletezi a formális verifikációs és kriptográfiai bizonyítási rendszereket, amelyeket a Reversible Scatter Flow (RSF) architektúra matematikai helyességének és végrehajtási integritásának biztosítására használnak. A rendszer két különböző megközelítést alkalmaz: Bel a strukturális tulajdonságok és a memóriabiztonság formális ellenőrzésére, valamint a Circom a ZK-SNARK-ok (Zero-Knowledge Succinct Non-Interactive Arguments of Knowledge) előállítására a helyes következtetés-végrehajtás bizonyítására.

### Bel formális verifikáció

A Bel specifikáció (rsf.bel) formális keretet biztosít az RSF modell strukturális invariánsainak ellenőrzéséhez. Egy rekurzív leszálló értékelőt használ a relatív biztonsági formula (RSF) különböző modellállapotok közötti ellenőrzésére.

### Magtípus meghatározások

A verifikációs motor alapvető Peano aritmetikai és logikai típusokat definiál a tenzorméretek és állapotátmenetek ábrázolására.

| Típus | Leírás | Kód Entitás |
| --- | --- | --- |
| nat | Peano természetes számok (z, s n) | LF nat |
| reg-state | A nyilvántartás életciklusának állapota (Alive/Freed) | LF reg-state |
| átmenet | Érvényes állapotátmenetek a memóriakezeléshez | LF átmenet |
| tensor-valid | Bizonyíték arra, hogy a dimenziók megegyeznek a teljes kiosztott mérettel | LF tensor-valid |

### Biztonsági invariánsok és alakellenőrzés

A Bel-t annak bizonyítására használják, hogy az olyan műveletek, mint a felosztás, összevonás és a visszafelé haladás konzisztens tenzoralakot és indexhatárokat tartanak fenn.

- Index határok: Az index-in-bounds predikátum biztosítja, hogy bármely B tétel és D dimenzió esetén a kiszámított lineáris index Idx szigorúan kisebb, mint a Teljes méret
- Felosztás/összevonás érvényessége: Ellenőrzi, hogy az RSF-csatolás felosztása (egy dimenzió két részre osztása) matematikailag konzisztens-e
- Nyilvántartási életciklus: Az átmenet típusa kikényszeríti, hogy egy registry handle csak akkor semmisíthető meg, ha érvényes állapotban van, megelőzve ezzel a double-free vagy use-after-free hibákat

### Bel Verification Logic Flow

A következő ábra azt szemlélteti, hogy a Bel hogyan hidalja át a "Memóriabiztonság" természetes nyelvi követelményeit a formális kód entitásokhoz.

### ZK-SNARK bizonyítékok (Circom)

Az inference_trace.circom fájl meghatározza azokat az áramköröket, amelyek szükségesek annak bizonyításához, hogy egy adott kimenetet egy adott modell és bemenet generált anélkül, hogy felfedné a modell súlyait vagy magát a bemenetet.

### Fixpontos aritmetika és Taylor-közelítés

Mivel a SNARK-ok véges mezőkön működnek, a lebegőpontos műveletek fixpontos skálázással és Taylor-soros közelítésekkel valósulnak meg.

- Méretezés: A fixpontos ábrázoláshoz $1,000,000$ állandó tényezőt használunk
- Exponenciális közelítés: Az RSF-skálázásban használt exp függvényt egy köbös Taylor-sorozat együtthatóival közelítjük:
- Lineáris: 1000
- Kvadratikus: 500
- Kocka: 167

### Kulcsáramkör sablonok

### RSFLayerComputation

Ez a sablon egyetlen RSF-réteg előrehaladását ellenőrzi. A sablon x bemenetet, súlyokat (weights_s és weights_t) vesz fel, és az affin csatolási transzformációt bizonyítja

### PoseidonChain

Egy kriptográfiai hashing segédprogram, amelyet nagy vektorok (mint például a modell súlyok vagy bemeneti tenzorok) áramkörön belüli elköteleződésére használnak. A bemeneteket feldarabolja és a Poseidon hash függvényen keresztül dolgozza fel

### RangeProof

Biztosítja, hogy az értékek a számítás során az érvényes numerikus korlátokon belül maradjanak, hogy megakadályozza a véges mezőben a túlcsordulást/alulcsordulást. A PedersenCommit-et használja az értékek bit-összetételének ellenőrzésére

### Adatáramlás: Következtetés nyomkövetés ellenőrzése

Az alábbi ábra mutatja az adatáramlást a Circom áramkörökön keresztül a FullInferenceProof előállításához.

### Kriptográfiai kötelezettségvállalások

A rendszer a PedersenCommit-ot használja az értékek elrejtésére, miközben lehetővé teszi, hogy az áramkör bizonyítsa a rájuk vonatkozó tulajdonságokat Ez elengedhetetlen a DifferentialPrivacyProof és SecureAggregationProof modulokhoz, amelyek biztosítják, hogy az egyes adat-hozzájárulások privátak maradjanak az elosztott képzés vagy következtetés során.

### Merkle Tree integráció

A VerifyMerkleProof sablon annak bizonyítására szolgál, hogy egy adott adatdarab egy nagyobb tételhez vagy modellállapothoz tartozik (az InferenceTraceWithBatch). Rekurzívan hash-olja a path_elemeket a Poseidon(2) segítségével, amíg a gyökeret el nem éri

| Komponens | Funkcionalitás |
| --- | --- |
| SafeIsZero | Korlátozás-biztonságos nulla-ellenőrzés |
| SafeIsEqual | Korlátozásbiztos egyenlőségi ellenőrzés |
| Mux1 | 1 bites multiplexer a Merkle-útvonal kiválasztásához |

## Fogalomtár

Ez az oldal a JAIDE (Reversible Scatter Flow) ökoszisztémára jellemző szakterminológia, rövidítések és architekturális fogalmak technikai definícióit tartalmazza.

### Építészeti alapfogalmak

### RSF (Reversible Scatter Flow)

A JAIDE alapvető idegi felépítése. A hagyományos transzformátorokkal vagy CNN-ekkel ellentétben az RSF egy bijektív (inverzív) architektúra, amely kereszt-affin csatolási rétegeken alapul. Lehetővé teszi a $O(1)$ memóriás visszaterjedést azáltal, hogy a bemeneti aktivációkat a kimenetekből rekonstruálja a visszaterjedés során.

- Végrehajtás: Amely a négy elsődleges paramétertenzort tartalmazza: s_weight, t_weight, s_bias és t_bias
- Matematikai primitív: $x_1$ a $x_2$ függvényével skálázódik, $x_2$ pedig a módosított $x_1$ függvényével fordítódik

### OFTB (Orthogonal Fractal Transform Block)

Egy paramétermentes keveredési réteg, amely Haar-wavelet pillangószerkezetet használ a globális kontextus és a térbeli keveredés biztosítására. Fix FRACTAL_SCALE $\approx 0.7071$ értékkel működik.

- Kódmutató: src/processor/oftb.zig
- Logika: SIMD @Vector(8, f32) a tenzorok felén végzett összeg- és különbség-műveletek elvégzésére

### SSI (strukturált szekvenciaindex)

Egy vödör alapú fa struktúra, amelyet nagy sebességű visszakeresésre és szekvenciaindexálásra használnak. Az adatokat szegmensekbe rendezi, és a kereséshez Hamming-távolságot vagy hash-alapú hasonlóságot használ.

- Adatszerkezet: Node objektumok fája, ahol minden csomópont 64 gyermekből álló bucket_countot tartalmaz
- Integritás: A Merkle-szerű hash-elést alkalmazza, ahol minden csomópont hash-ja a gyermekei vagy szegmensei hash-jainak összege

### MGT (Morpheme-Guided Tokenizer)

Hibrid tokenizáló, amely a morfológiai dekompozíciót (előtagok, gyökök, utótagok) BPE (Byte Pair Encoding) fallbackkel kombinálja. Kifejezetten az olyan agglutináló nyelvekre van hangolva, mint a magyar, miközben fenntartja az angol kompatibilitást.

- Alkatrészek: Fenntartja az előtagok, utótagok és gyökök térképeit
- Logika: Az initMorphemes függvény feltölti ezeket a térképeket nyelvspecifikus töredékekkel

### Rendszer leképezése: Természetes nyelvből kódolt entitásokba

A következő ábrák a fogalmi területet a kódbázisban található konkrét végrehajtási részletekkel hidalják át.

### 1. ábra: RSF csővezeték adatáramlás

Ez az ábra a logikai "Forward Pass"-t a Zig és a Futhark implementációkban található konkrét függvényekhez és tenzorokhoz rendeli hozzá.

### 2. ábra: NSIR tudásgráf entitásai

A "Quantum-Relational" fogalmak leképezése az nsir_core.zig implementációra.

### Optimalizálás és képzés feltételei

### SFD (sztochasztikus Fisher-diagonális)

A JAIDE elsődleges optimalizálója. A Fisher Információs Mátrix diagonálisát becsüli a természetes gradiensfrissítések elvégzéséhez, ami hatékonyabb az RSF bijektív geometriájához, mint a standard Adam.

- Végrehajtás: Zig.
- Kulcsfunkció: fisher_diagonal_update a Futharkban

### SophiaSOAP

Az optimalizáló kiterjesztése, amely Hutchinson Hessian becslést tartalmaz a másodrendű konvergencia tulajdonságai érdekében.

- Kódmutató: Az SFD modul logikájába integrált görbületbecslés.

### Műszaki rövidítések

| Betűszó | Teljes név | Leírás | Kódmutató |
| --- | --- | --- | --- |
| NSIR | Nem lineáris önhasonló információkeresés | A kvantum-relációs gráf alrendszer. | src/core_relational/ | src/core_relational/
| CREV | Contextual Relational Extraction & Validation | Pipeline a nyers adatok NSIR-be történő beviteléhez. | src/core_relational/crev.zig |
| ESSO | Entangled Stochastic Symmetry Optimizer | Globális optimalizáló gráftopológiához. | src/core_relational/esso.zig |
| OFTB | Orthogonal Fractal Transform Block | Paramétermentes Haar-wavelet keverési réteg. | src/processor/oftb.zig | src/processor/oftb.zig
| RSF | Reversible Scatter Flow | Az alapvető bijektív neurális architektúra. | src/processor/rsf.zig |
| SSI | Structured Sequence Index | A nagysebességű vektor/szekvencia adatbázis. | src/index/ssi.zig |


 1. Bevezet-e az RSF egy alapvetően új számítási primitív elemet?

IGEN: A primitív elem a kereszt-affin kapcsolás: a `computeScaleRow` kiszámítja az `exp(clip(W_s·x2 + b_s))` értéket, és megszorozza az `x1`-et; a `computeTranslationRow` kiszámítja a `W_t·y1 + b_t` értéket, és hozzáadja az `x2`-hez. Ez nem egy meglévő primitív módosítása.  

A `LayerCore` struktúra kizárólag `s_weight`, `t_weight`, `s_bias`, `t_bias` elemeket tartalmaz — nincs figyelemmátrix, nincs konvolúciós kernel, nincs rejtett állapot.  

A Twelf bizonyítás a `layer-weights`-et a következőképpen definiálja: `mk-lw : {D:nat} mat D D -> mat D D -> vec D -> vec D -> clip-range -> layer-weights` — pontosan 2 súlymátrix + 2 biasvektor + clip-range, semmi más.  

---

 2. Az RSF meghatározza-e a meglévő architektúrákra nem redukálható, különálló információáramlási topológiát?

IGEN: A topológia a következő: a bemenet felosztása `(x1, x2)`-re, `x1` transzformálása `x2` függvényében, `x2` transzformálása a módosított `x1` függvényében. Ez a keresztkapcsolás szerkezetileg eltér az önfigyeléstől (`Q·K^T·V`), a konvolúciótól (helyi befogadó mező) vagy a rekurziótól (szekvenciális állapot). Az `inverseInPlace` a pontos algebrai inverz – ez a Transformer átkötésével nem érhető el.  

A Twelf `coupling-invertibility` bizonyítása igazolja, hogy ez a topológia típus szinten bijektív.  

---

 3. Mutat-e az RSF az architektúrájából fakadó új skálázási törvényt?

IGEN: A `calculateTotalParams` rétegenként `dim² × 4 + dim × 2` értéket számol ki – pontosan 4 súlymátrixot + 2 bias-t. A visszafelé irányuló lépés O(1) memóriát igényel, függetlenül a rétegek számától: a `backwardOnCore` újra futtatja a `forwardOnCore`-t a bemeneten, majd fordított sorrendben végigfut a rétegeken, meghívva a `backwardFromOutputs`-t, amely a kimenetekből inline módon rekonstruálja az `x1`/`x2`-t — aktivációs tárolás nélkül.   

A Cryptol specifikáció megerősíti: `calculateTotalParams dim rétegek = (dim_sq * 4 + dim * 2) * rétegek`.  

---

 4. Rendelkezik-e az RSF független reprezentációs bias-szal?

IGEN: Az induktív torzítás bijektív kereszt-affin kapcsolás: a skála `x2`-re vonatkozik, hogy `x1`-et transzformálja; a transzláció a módosított `x1`-re vonatkozik, hogy `x2`-t transzformálja. Ez egy keresztkapcsolási torzítás, amely az összes korábbi családból hiányzik. Az `OFTB` hozzáad egy paramétermentes Haar-wavelet szórási torzítást (`fractal_scale = 0.70710678`).  

---

 5. Bevezet-e az RSF új aszimptotikus viselkedést a memóriában, a kommunikációban vagy a számításban?

IGEN: O(1) visszafelé irányuló memória: a `backwardFromOutputs` csak `y1`-et, `y2`-t (kimeneteket) és `dy1_in`-t, `dy2_in`-t (gradiensek) fogad. Inline módon rekonstruálja az `x2_row[d] = y2_row[d] - trans_sum` és az `x1_row[d2] = y1_row[d2] / scale` értékeket. A rétegek között nem tárolnak aktivációs tenzorokat.  

A Futhark GPU-kernel, az `rsf_backward_flow` tárolt aktivációk nélkül is képes rekonstruálni a kimeneteket.  

---

 6. Általánosan alkalmazható-e az RSF számos területen?

IGEN: A kód bemutatja: szöveg (magyar JSONL a `HuggingFaceFW/finephrase` segítségével), több GPU-s képzés, következtetési szerver, ZK-bizonyítékok, kvantumintegráció. A `FullInferenceProof` circom sablon elfogadja a `tokens[dim]` és a `layer_weights_s/t[num_layers][dim][dim]` — területfüggetlen bemeneteket.  

Az `rsf_relational_context` Futhark függvény RSF-kapcsolást alkalmaz tetszőleges szekvenciaadatokra.  

---

 7. Szolgálhat-e az RSF univerzális gerinchálózat-családként?

IGEN: A kódbázis 5 különböző belépési pontot tartalmaz, amelyek az RSF-et használják gerincként: `main.zig` (interaktív/edzés), `main_gpu.zig` (egy H100, `dim=2048, layers=48`), `main_distributed_futhark.zig` (több GPU-s B200, NCCL), `inference_server_main.zig` (HTTP API) és `main_distributed.zig` (CPU-el osztott).   

---

 8. Kialakulhat-e az RSF-ből egy származtatott modellekből álló ökoszisztéma?

IGEN: A kódbázis már tartalmazza: RSF + OFTB scatter, RSF + NSIR moduláció (`nsirModulateInPlace` `NSIR_MODULATION_FACTOR = 1.05` értékkel), RSF + SFD optimalizáló, RSF + SophiaSOAP, RSF + ZK bizonyítékok, RSF + kvantumintegráció. A `flattenRSFParams` azt mutatja, hogy az RSF paraméterei laposak és összetették.   

---

 9. Megmarad-e az RSF architektúrájának identitása a különböző implementációk és modellméretek között?

IGEN: Ugyanaz a 4-tenzoros szerkezet azonos formában jelenik meg a következőkben:
- CPU Zig: `LayerCore`, amely tartalmazza az `s_weight`, `t_weight`, `s_bias`, `t_bias` elemeket
- GPU Futhark F32: az `rsf_flow` elfogadja az `s_weight`, `t_weight`, `s_bias`, `t_bias` értékeket
- GPU Futhark F16: a `training_step` elfogadja a `weights_s`, `weights_t`, `s_bias`, `t_bias` értékeket
- ZK áramkör: a `FullInferenceProof` a `layer_weights_s`, `layer_weights_t` paramétereket használja
- Cryptol: az `RSFLayer` típusnak vannak `s_weight`, `t_weight`, `s_bias`, `t_bias` paraméterei   

---

 10. Az RSF egyértelműen elkülöníthető-e az optimalizálási vagy a képzési trükköktől?

IGEN: A `LayerCore.forwardInPlace` és az `inverseInPlace` nem tartalmaz optimalizáló kódot. Az SFD optimalizáló egy teljesen különálló modul. Az OFTB egy különálló modul. Az RSF bijektivitása az optimalizálótól függetlenül érvényes — a `verifyInvertible` ezt futásidőben ellenőrzi, függetlenül bármilyen edzési állapottól.  

---

 11. Bevezet-e az RSF új mechanizmust a kontextusintegrációhoz?

IGEN: Az `rsf_scatter` Futhark függvény megvalósítja a Haar-wavelet pillangókeverést: `inv_sqrt2 * (x[j] + x[j+half])` az összegek esetében, `inv_sqrt2 * (x[j] - x[j+half])` a különbségek esetében, rétegenként változó permutációs indexekkel. Ez globális kontextust biztosít O(N²) figyelem nélkül.  

---

 12. Bevezet-e az RSF új mechanizmust a relációs vagy hierarchikus feldolgozáshoz?

IGEN: A `SelfSimilarRelationalGraph` (NSIR) `EdgeQuality` típusokkal (`superposition`, `entangled`, `coherent`, `collapsed`, `fractal`) kvantumállapot-relációs feldolgozást biztosít az RSF aktivációk tetején. A `ReasoningOrchestrator` háromszintű hierarchikus következtetést futtat (`fast_inner_steps=50`, `slow_outer_steps=10`, `hierarchical_depth=3`).   

---

 13. Meghatározza-e az RSF a saját induktív torzítások osztályát?

IGEN: Három különböző induktív torzítás a kódból:
1. Bijektív kereszt-affin kapcsolás — az információ nem összeomolhat (bizonyítva a Mizar `ThForwardInverseIdentity`-ben)
2. Paramétermentes Haar-wavelet szórás — OFTB `fractal_scale = 0.70710678` értékkel, tanulható paraméterek nélkül
3. Klip-határolt skála gradiens — `ds_row[d2] = 0.0` a klip tartományon kívül, strukturális gradiens robusztusság  

---

 14. Az RSF képes-e az architektúrájának köszönhetően bizonyos problématípusoknál jobb teljesítményt nyújtani a korábbi családoknál?

Architektúra szempontjából igen, a „fix VRAM-méret mellett változó mélység” esetében. Az O(1) visszafelé irányuló memóriaterhelés azt jelenti, hogy az RSF tetszőleges számú réteggel képes tanulni fix VRAM-méret mellett. A `main_gpu.zig` a H100-on (80 GB) `dim=2048, layers=48` beállításokat használ; az elosztott tréner a B200-at (192 GB) célozza meg. Az azonos VRAM-kapacitással rendelkező Transformer-t az O(L) aktivációs tároló korlátozza. Hogy ez a feladat teljesítményében is megmutatkozik-e, azt a kód nem bizonyítja.  

---

 15. Van-e az RSF-nek elméleti alapja, amely megmagyarázza, miért viselkedik másképp?

IGEN: Négy független formális bizonyítás:

- Mizar `ThForwardInverseIdentity`: 17 lépéses algebrai bizonyítás (A5–A17), miszerint `InverseInPlace(ForwardInPlace(x1,x2)) = (x1,x2)`. `ThCoreForwardInverseIdentity`: teljes modellszint.
- Twelf `coupling-invertibility`: a bijekció típuselméleti bizonyítása.
- Lean 4 `FloatInterface`: több mint 40 axióma, beleértve a `divF_mulF_inv` és a `mulF_divF_cancel` axiómákat, amelyek lehetővé teszik az inverz bizonyítás működését.
- Beluga regiszterállapot-gép: `reg-alive`, `reg-freed`, `transition` típusok, amelyek bizonyítják, hogy a szabadítás utáni használat strukturálisan lehetetlen. 

---

16. Az RSF jelentősen eltérő kifejezőképességet biztosít-e a korábbi architektúrákhoz képest?

IGEN: A bijektív korlátozás azt jelenti, hogy az RSF nem tudja összevonni az információkat – minden bemenet egy egyedi kimenethez rendelődik (bizonyítva). A transzformátorok összevonhatják az információkat (az attention az összes súlyt egy tokenhez rendelheti). A `verifyInvertible` futásidejű ellenőrzés ezt strukturálisan is megerősíti. A Lean 4 `FloatInterface.divF_mulF_inv` axióma az algebrai alapja ennek. 

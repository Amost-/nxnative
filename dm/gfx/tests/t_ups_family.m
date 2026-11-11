// Resolution upscaling of an alias family: a render target the game describes at several sizes over one storage, as a game with dynamic resolution does (Bayonetta Origins' 13
// scene targets of 1600x900 are all such families). A family is scaled as a whole or not at all (ups_family / ups_pick in nvn_mtl.m), and its members keep sharing one placement
// heap, made for the scaled sizes (image_texture). The factor comes from DM_UPSCALE, read once at start-up, so the check recipe runs this at 1, 1.5 and 2: at 1 nothing is scaled
// and the families are what t_image_alias checks.
#include "../nvn/nvn_mtl.m"
void *front_metal_layer(void) { return NULL; }
module_t *module_of(const void *p) { (void)p; return NULL; }
module_t *g_mod; int g_nmod;
void svc_thread_dump(void) {}
uint64_t now_ns(void) { return bp_now(); }
static int checks, failed;
#define CHECK(c, label) do { checks++; if (!(c)) { failed++; fprintf(stderr, "FAIL: %s\n", label); } } while (0)

// An image-shaped texture description (COMPRESSIBLE | IMAGE, 2D, one level: image_shape) of w x h at offset off of the pool, as the game's render targets are described
static tex_t image(pool_t *pool, uint64_t serial, uint64_t off, unsigned w, unsigned h) {
    tex_t t = {.magic=MAGIC('T','E','X',0), .serial=serial, .pool=pool, .mem=pool->mem+off, .off=off};
    t.d = (nvn_texdesc){.target=NVN_TEXTURE_TARGET_2D, .format=NVN_FORMAT_RGBA8, .flags=NVN_TEXTURE_FLAGS_COMPRESSIBLE|NVN_TEXTURE_FLAGS_IMAGE,
                      .width=w, .height=h, .depth=1, .levels=1, .samples=1};
    nvn_tex_layout(&t.d, &t.L); return t;
}
// The size the host gives a dimension of a scaled texture (ups_dim in nvn_mtl.m), at factor f
static NSUInteger scaled(unsigned n, double f) { return (NSUInteger)MAX(lround(n * f), 1L); }

int main(void) { @autoreleasepool {
    mtl_init(); void *mem=NULL;
    // 64 MiB of pool memory: three families at offsets 0, 24 MiB and 48 MiB, each far from the next (the largest description, 1600x900 RGBA8, takes under 6 MiB)
    posix_memalign(&mem,16384,64<<20); memset(mem,0,64<<20);
    double f=ups_factor();
    @autoreleasepool {
    mtl_sub_begin();
    pool_t pool={.magic=MAGIC('P','O','O','L'), .flags=NVN_MEMORY_POOL_FLAGS_CPU_NO_ACCESS|NVN_MEMORY_POOL_FLAGS_GPU_CACHED|NVN_MEMORY_POOL_FLAGS_COMPRESSIBLE, .mem=mem, .size=64<<20};

    // A screen-sized family with a member too small to be scaled by its own size (256x144 is under the 320x180 of the size rule). The small member is resolved first: the
    // family's largest live description decides, so the order the game uses its sizes in does not matter
    tex_t big=image(&pool,995000,0,1600,900), mid=image(&pool,995001,0,1280,720), tiny=image(&pool,995002,0,256,144);
    mtl_tex_init(&big); mtl_tex_init(&mid); mtl_tex_init(&tiny);
    id<MTLTexture> tt=tex_mtl(&tiny), tm=tex_mtl(&mid), tb=tex_mtl(&big);
    CHECK(tt && tm && tb,"every member of a screen-sized family has a texture");
    CHECK(tb.width==scaled(1600,f) && tb.height==scaled(900,f),"the largest member is made at its size times the factor");
    CHECK(tm.width==scaled(1280,f) && tm.height==scaled(720,f),"a smaller member is scaled by the same factor");
    CHECK(tt.width==scaled(256,f) && tt.height==scaled(144,f),"a member under the size rule's minimum is scaled with its family");
    CHECK(tb.heap!=nil && tm.heap==tb.heap && tt.heap==tb.heap,"scaled or not, the members share one heap");
    MTLTextureDescriptor *ld=tex_desc(&big,0); ld.width=scaled(1600,f); ld.height=scaled(900,f);
    CHECK(tb.heap.size>=[g_dev heapTextureSizeAndAlignWithDescriptor:ld].size,"the heap holds the largest member at the size it is made at");
    CHECK(ups_of(&big,tb)==(f>1?(float)f:1) && ups_of(&tiny,tt)==(f>1?(float)f:1),"every member reports the family's factor");

    // A family whose largest description is no screen-like target (1024x512: an aspect of 2.0, outside the size rule) stays whole at the game's size, although a member
    // of it (640x360) would be scaled by its own size
    tex_t wide=image(&pool,995010,24<<20,1024,512), ok=image(&pool,995011,24<<20,640,360);
    mtl_tex_init(&wide); mtl_tex_init(&ok);
    id<MTLTexture> to=tex_mtl(&ok), tw=tex_mtl(&wide);
    CHECK(to.width==640 && to.height==360 && tw.width==1024 && tw.height==512,"a family whose largest member is not screen-like stays at the game's size");
    CHECK(tw.heap!=nil && to.heap==tw.heap && tw.heap!=tb.heap,"that family shares a heap of its own");

    // A single description of the same shape is no family: it is scaled alone, outside any heap, as before
    tex_t solo=image(&pool,995020,48<<20,1600,900); mtl_tex_init(&solo);
    id<MTLTexture> ts=tex_mtl(&solo);
    CHECK(ts.width==scaled(1600,f) && ts.height==scaled(900,f),"a single description is scaled by its own size");
    CHECK(f>1 ? ts.heap==nil : 1,"a scaled texture outside a family is not placed in a heap");

    mtl_sub_commit(); mtl_drain();
    CHECK(!mtl_last_commit_error(),"making and zero-filling the families completes without GPU error");
    tex_t *all[]={&big,&mid,&tiny,&wide,&ok,&solo};
    for (int i=0;i<6;i++) mtl_tex_release(all[i]);
    mtl_alias_drop_pool(&pool);
    }
    // the released textures and their heaps go once the GPU and the deferred releases are done with them (as t_image_alias waits)
    mtl_sub_begin(); mtl_sub_commit(); mtl_drain(); mtl_sub_begin(); mtl_sub_commit(); mtl_drain();
    dispatch_sync(g_feedback_q,^{}); defer_drain();
    CHECK(g_image_heap_n==0,"every family heap is released after its textures go");
    free(mem);
    printf("upscaled alias families (%gx): %d checks, %d failed\n",f,checks,failed); return failed!=0;
} }

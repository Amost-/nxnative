// DM_NVN_MESHLOG_CB_GPU: a task draw's uniform words copied by the GPU in queue order (mlcb_gpu_copy), next to what the CPU read when the draw was encoded (subrec_mesh_words)
#include "../nvn/nvn_mtl.m"
void *front_metal_layer(void) { return NULL; }
module_t *module_of(const void *p) { (void)p; return NULL; }
module_t *g_mod; int g_nmod;
void svc_thread_dump(void) {}
uint64_t now_ns(void) { return bp_now(); }
static int checks, failed;
#define CHECK(c, label) do { checks++; if (!(c)) { failed++; fprintf(stderr, "FAIL: %s\n", label); } } while (0)

int main(void) { @autoreleasepool {
    setenv("DM_NVN_MESHLOG_CB", "2:16", 1); setenv("DM_NVN_MESHLOG_CB_GPU", "1", 1);
    mtl_init();
    void *mem = NULL; if (posix_memalign(&mem, getpagesize(), getpagesize())) return 1;
    memset(mem, 0, getpagesize()); mtl_pool_add(mem, getpagesize());
    uint32_t *w = mem; w[4] = 1; w[5] = 2; w[6] = 3; w[7] = 4;
    NvShader *ts = [NvShader new];
    mtl_sub_begin(); state_reset(); memset(&R, 0, sizeof R);
    S.ubo[3][2] = (p_bind_buf){.addr = (uint64_t)mem, .size = 1024};
    subrec_t *r = g_subrec_cur; CHECK(r != NULL, "the submission has a record");
    mlcb_gpu_copy(ts);
    const volatile uint32_t *slot = g_mlcb_gw; CHECK(slot != NULL, "the copy handed out its slot");
    CHECK(slot && slot[0] == 0xfeedface && slot[3] == 0xfeedface, "the slot says 'not run' until the GPU has copied");
    subrec_mesh_add("a5288d0a6c4971fd", "a80a03d4747a70c7", "de4c1ebffd6c3960", 12, 3, NULL);
    subrec_mesh_words(S.ubo[3]);
    CHECK(g_mlcb_gw == NULL && r->m[0].gw == slot && r->m[0].has_words, "the record took the slot once");
    CHECK(r->m[0].words[0] == 1 && r->m[0].words[3] == 4, "the CPU's words are those at encode time");
    w[4] = 9; w[5] = 9; w[6] = 9; w[7] = 9;   // written after the draw was encoded, before the GPU ran it: the GPU copy sees this, the CPU's words do not
    uint64_t fence = mtl_sub_commit(); CHECK(mtl_wait(fence, 2000000000ull), "the copy completes"); mtl_drain();
    CHECK(!mtl_last_commit_error(), "no GPU error");
    CHECK(slot && slot[0] == 9 && slot[1] == 9 && slot[2] == 9 && slot[3] == 9, "the GPU copied the memory as it was when it ran");
    CHECK(r->m[0].words[0] == 1, "the CPU's words stay the encode-time ones");
    char buf[SUBREC_LINE]; subrec_mesh_fmt(buf, sizeof buf, r);
    CHECK(strstr(buf, "words 0x1 0x2 0x3 0x4 at +16") && strstr(buf, "; now 0x9 0x9 0x9 0x9; GPU copy ahead of the draw 0x9 0x9 0x9 0x9)"), "the report prints all three");
    printf("t_mlcb_gpu: %d checks, %d failed\n", checks, failed); return failed != 0;
} }

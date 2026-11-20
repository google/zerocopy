/* G1-G8: unused-result diagnostics in GCC (C23 mode). */
__attribute__((warn_unused_result)) int legacy(void) { return 1; }
[[nodiscard]] int modern(void) { return 1; }
[[nodiscard("check the status")]] int modern_reason(void) { return 1; }
typedef int (*fp_t)(void);
#define CALL_LEGACY() legacy()
int plain(void) { return 1; }

void cases(void) {
    legacy();             /* G1 GNU attribute, bare call            */
    (void)legacy();       /* G2 GNU attribute, cast to void         */
    modern();             /* G3 C23 [[nodiscard]], bare call        */
    (void)modern();       /* G4 C23 [[nodiscard]], cast to void     */
    modern_reason();      /* G5 C23 [[nodiscard("...")]]            */
    fp_t f = legacy; f(); /* G6 call through a function pointer     */
    CALL_LEGACY();        /* G7 call via macro                      */
    plain();              /* G8 unannotated function                */
    if (legacy()) {}      /* G9 result used in a condition          */
}

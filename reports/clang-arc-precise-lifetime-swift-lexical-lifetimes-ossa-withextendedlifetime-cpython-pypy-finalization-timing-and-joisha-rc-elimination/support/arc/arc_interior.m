// arc_interior.m -- IR-only probe of ARC's interior-pointer rule.
__attribute__((objc_root_class))
@interface Buf
- (char *)bytes __attribute__((objc_returns_inner_pointer));
@end
extern Buf *buf_new(void) __attribute__((ns_returns_retained));
extern void consume(char *p);
extern void note(const char *msg);

void interior_imprecise(void) {
  Buf *b = buf_new();
  char *p = [b bytes];
  note("after bytes");
  consume(p);
}
void interior_precise(void) {
  __attribute__((objc_precise_lifetime)) Buf *b = buf_new();
  char *p = [b bytes];
  note("after bytes");
  consume(p);
}

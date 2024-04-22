/* Make sure you have C linkage when defining in c++ file */
#ifdef __cplusplus
extern "C"
#endif
    void
    _DYNAMIC() {
  /* Either leave empty, or infinite loop here */
  while (1)
    __asm volatile("NOP");
}
#ifdef __cplusplus
extern "C"
#endif
    void
    _init(void) {
  ;
}

// C++17/20 [[nodiscard]] on functions, types, and constructors.
struct [[nodiscard]] Status { int code; };
Status op();
[[nodiscard]] int f();
struct Guard { [[nodiscard]] Guard(int); };
template <class F> auto call(F fn) { return fn(); }
void cases() {
    f();                 // P1 nodiscard function
    (void)f();           // P2 cast to void
    op();                // P3 nodiscard type returned by value
    Status& r = *new Status{0}; (void)r; 
    call(f);             // P4 through a generic wrapper returning int
    call(op);            // P5 through a generic wrapper returning Status
    Guard(1);            // P6 nodiscard constructor (C++20)
    static_cast<void>(op()); // P7 static_cast<void>
    [[maybe_unused]] auto x = f(); // P8 bound to maybe_unused variable
}

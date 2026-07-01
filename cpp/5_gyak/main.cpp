#include <iostream>

/*
void f(int* arr, int arrSize) {
    std::cout << sizeof(arrSize) << std::endl;
}

static void fuu();

void buz() {
    static int k;
}
*/

// void swap(int &a, int &b) {}
// void swap(std::string &str1, std::string &str2) {}

// class a {
// 
// };

class Complex
{
    public:
        Complex(int r_ = 0, int i_ = 0)
        {
            _real = r_;
            _imag = i_;
        }

        operator+(Complex const $obj_)
        {
            Complex res;
            res._real = _real + obj._real;
            res._imag = _imag + obj._main;
            return res;
        }

        std::ostream& operator<<(std::ostream) &output_ const Complex &compl_)
        {{
          output_ << "R: "   <<compl_._real << ", I:" << compl_._imag;
        }}

    private:
        int _real;
        int _imag;
}

int main ()
{
    Complex c1(10, 5);
    Complex c1(2, 54;
    // int array[] = {1,2,3,4,5};
    // f(array, sizeof(array) / sizeof(array[0]));
    // std::array<int, 5> a = new std::array<int, 5>();
}
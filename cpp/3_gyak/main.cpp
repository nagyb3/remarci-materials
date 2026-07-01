/*
void symbol();

namespace A {
    int i = 9;

    class MyClass {};
}

namespace B {
    int i = 10;
}

namespace {
    int j = 11;
}

namespace hosszuNamespaceNev {}
namespace hNN = hosszuNamespaceNev;

//using namespace A;
//using namespace B;


int main() {
    A::i;
    B::i;
    ::j;

    symbol();
}
*/

#include <iostream>

//int x;

//std::ostream& os = std::cout << "Hello";

/*
void foo() {
    int static x = 0;
    ++x;
    std::cout << x <<std::endl;
}
*/

void f(char* b) { std::cout << "char" << std::endl; }
void f(bool b) { std::cout << "boolean" << std::endl; }

int main() {
    //f(NULL);
    f(nullptr);

    /*
    int i = 0;
    int* iPtr = &i;
    int** piPtr = &iPtr;
    */

    int i, j;
    int* p = &i;
    int** q = &p;

    *q = &j;

    int k = 1;
    int& rk = k;
    rk = 123213;
    int l = 1;
    rk = l; // NEM JÓ!!!


    //or (int i = 0; i < 5; ++i) foo();
    //std::cout << " world! :D";

    //int* i = new int(1);
    //delete i;

    //int* pArray = new int[0];
    //delete[] pArray;

    //const int i = 1;
    //int i=(2);

    //constexpr int h = 2;,
    
    //#define NULL 0
    /*
    int* ptr4 = NULL;
    int* ptr5 = 0;
    int* ptr6 = nullptr;
    */
}


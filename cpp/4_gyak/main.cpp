#include <iostream>

void swapPointer(int* a, int* b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

void swapReference(int &a, int &b)
{
    int tmp = a;
    a = b;
    b = tmp;
}

std::string& concat(std::string& str_)
{
    return str_ += "world";
    //std::string str = str_ + "world!";
    //return str;
}

int multiply(int a, int b) { return a * b; }
void helper(int a, int b, int(*fptr)(int, int))
{
    std::cout << fptr(a, b) << std::endl;
}


int main()
{
    typedef int(*Multiply)(int, int);
    //using Multiply = int(*)(int, int) // cpp11 using
    Multiply mult = multiply;
    //int (*mult)(int, int) = multiply;
    helper(1, 5, multiply);    
    mult(1,2);
    /*
    std::string str = "Hello ";
    std::cout << concat(str) << std::endl;
    
    int c = 1;
    int d = 2;
    std::cout<< a << " "<< b << std::endl;
    swapPointer(&c, &d);
    swapPointer(c, d);
    std::cout<< a << " "<< b << std::endl;

    int i = 1;
    int* const cPtrI = &i;
    const int * cPtrI = &i;
    const int * const ccPtrI = &i;

    int i, j;
    int* p = &i;
    int* const * q = &p;
    int* const **const r = &q;

    int** q = &p;
    *q = &j;

    //array[11];

   int array[] = {1, 2, 3, 4, 5};
   array[0] == *(array+0) == *(0+array) == 0[array];
   int t[][3] = {{1,2,3}, {4,5,6}, {7,8,9}};
   t[1][0] == *(*(t+1)+0) == *(1[t]+0);

   */
   //std::cout << sizeof(array) << " " << sizeof(int) << std::endl;
   // sizeof(array) / sizeof(array[0])
   //array[6] = 5; -fsanitize=address
}
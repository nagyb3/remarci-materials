#include <iostream>

using namespace std;

int f() { std::cout << "f()" << std::endl; return 1; }

int main(int argc, const char* argv[]) {
    int i = 0;
    int j = 0;

    //std::cout << f();

    std::cout << ++i << ++j << std::endl;

    //std::cout << "Henlo fren" << std::endl;

    return 0;
}
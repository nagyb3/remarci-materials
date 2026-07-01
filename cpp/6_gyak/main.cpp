#include <iostream>

/*
struct Student {
    int age;
    double weight;
    int height;
};

class  MyClass {
    int age;
};

class  MyClass2 : private MyClass{
    int age;
};
*/

// [9, *] -> [16, *] -> [4, *] -> [1, /]

/*
struct List {
    int data;
    List* next;
};
*/

class MyClass {
    MyClass() {}
    MyClass(int a_) { _a = a_; } // oaram ctor
    MyClass(const MyClass& obj_) {};
    //MyClass(int&& a_) {_a(std::move(a_)) } // C++11
    
    int _a;
};

class A {
    public:
    A() {_x = 0;}
    A(int x_) {_x = x_;}

    void setX(int x_) {
        if (x_ <= 0) return;
        _x = x_;
    }

    int getX() { return _x; }
    
    private:
    int _x;
};

class B {
    public:
    // B() : {_a._x = 3;} // def constructor --> param constructor
    B() : _a(3) {}
    A _a;
};

class C {
    C (int a, int c) : x(a), y(c) {}
    const int x;
    int& y;
};

int main() {

/*
List* head = new List;
head->data = 9; // (*head).data = 9;
head->next = new List;
head->next->data = 16;
head->next->next = new List;
head->next->next->data = 23;
head->next->next->next = 0; // C++11 óta jó nullptr helyett

// ... sok törlés és ismétlés
delete head->next->next;
delete head->next;
delete head;

List* add(List* head, int data) {
    if (head == 0) {
        List* ret = new List;
        ret->data = data;
        ret->next = 0;
        return ret;
    }
    // Még nem vagyunk a lista végén, akkor meghívjuk rekurzívan az add függvényt a követkző lista elemmel és az adattal
    head->next = add(head->next, data);
    return head;
}

void free(List* head) {
    if (head == 0) {
        return;
    }
    free(head->next);
        delete head;
}
*/

/*
    std::cout << sizeof(double) << std::endl;
    std::cout << sizeof(int) << std::endl;
    std::cout << sizeof(Student) << std::endl;

    Student s2;
    s2.age;
    s2.weight;

    MyClass mc1;
    // mc1.age;

*/

    //int pi = 3.14;

    // for (double d = 0.0; d != 1; d += 0.1) {
        // std::cout << d << std::endl;
    // }

    //std::string = "hello";
    //str[0] = "b";
    //const char* = ""; [h e l l o \0]
}
#include <iostream>
#include <vector>
#include "animal.hpp"

using namespace std;

int main(){
    //Animal a("sanyi", 10);
    Animal* a;
    a = new Zebra("Karcsi",10,1001);
    a->print(); //*a.print();

    ////////////////////////////////
    Animal* b;
    string tmp;
    cin >> tmp;
    if (tmp == "zebra"){
        b = new Zebra("Karcsi",10,1001);
    } else {
        b = new Dog("Karcsi",10,"Emanuel");
    }
    b->print();

    ////////////////////////////////
    vector<Animal*> as;
    as.push_back(new Zebra("Gyuri",10,100));
}
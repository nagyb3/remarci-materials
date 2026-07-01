#include <iostream>
#include <fstream>
#include "cactusenor.hpp"

using namespace std;

int main()
{
    //Írjuk ki a szúrós kaktuszok neveit!
    CactusEnor e("inp.txt");

    e.first();
    while (!e.end()){
        cout << e.current() << endl;
        e.next();
    }

    //Helyezzük egymásra a kaktuszokat! Milyen magasak így?
    CactusEnor e2("inp.txt");
    
    int sum = 0;
    e2.first();
    while (!e2.end()){
        sum += e2.current().height;
        e2.next();
    }

    cout << "Sum of height is: " << sum << endl;
    return 0;
}
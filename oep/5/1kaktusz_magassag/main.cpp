#include <iostream>
#include <fstream>
#include "cactusheightenor.hpp"

using namespace std;

int main()
{
    //Soroljuk fel a kaktuszok magasságait!
    CactusHeightEnor e("inp.txt");

    e.first();
    while (!e.end()){
        cout << e.current() << endl;
        e.next();
    }

    //Helyezzük egymásra a kaktuszokat! Milyen magasak így?
    CactusHeightEnor e2("inp.txt");
    
    int sum = 0;
    e2.first();
    while (!e2.end()){
        sum += e2.current();
        e2.next();
    }

    cout << "Sum of height is: " << sum << endl;
    return 0;
}
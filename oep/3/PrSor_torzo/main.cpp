//Készítette:    Veszprémi Anna
//Dátum:         2019.02.19.
//Feladat:       Prioritásos sor megvalósítása rendezetlen tömbbel.
//               Menürendszer készítés a típus műveleteinek kényelmes kipróbálásához.
//               Automatikusan futtatható tesztesetek készítése a catch.hpp segítségével.
//Felhasznált header fájl: read.hpp (ellenőrzött beolvasás billentyűzetről, szerző: Gregorics Tibor)

#include <iostream>
#include <vector>
#include "menu.h"

using namespace std;

int main()
{
    cout << "Prioritasos sor" << endl;

    Menu teszt;
    teszt.run();

    return 0;
}

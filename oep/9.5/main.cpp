#include <iostream>
#include <fstream>

#include "naprendszer.h"
#include "bolygo.h"
#include "csillaghajo.h"

using namespace std;



int main()
{
    Naprendszer* nr = Naprendszer::Instance();

    Bolygo* fold   = new Bolygo("Fold");
    Bolygo* mars   = new Bolygo("Mars");
    Bolygo* venusz = new Bolygo("Venusz");

    nr->bolygok[0] = fold;
    nr->bolygok[1] = mars;
    nr->bolygok[2] = venusz;

    Csillaghajo* cs1 = new Faltoro("elso", 3, 3, 3);
    cs1->ved(fold);
    Csillaghajo* cs2 = new Partraszallo("masodik", 1, 1, 1);
    cs2->ved(venusz);

    Csillaghajo* hajo;
    if (nr->maxTuzero(hajo)){
        cout << "Max tuzero: " << hajo->nev << endl;
    } else {
        cout << "Nincs csillaghajo a bolygoval\n";
    }

    cout << "Fold pajzsa: " << fold->osszPajzs() << endl;

    if (nr->vedtelen() != nullptr){
        cout << nr->vedtelen()->nev << " vedtelen\n";
    } else {
        cout << "Nincs vedtelen bolygo" << endl;
    }

    return 0;
}




/*int main()
{
    Naprendszer* ss = Naprendszer::Instance();

    ifstream f("input.txt");
    if(f.fail()) return 1;

    string planetname, shipname, type;
    int n, m, s, a, g;

    f >> n;
    for(int i = 0; i<n; ++i){
        string planet;
        f >> planetname >> m;
        Bolygo *pl = new Bolygo(planetname);
        for(int j = 0; j<m; ++j){
            f >> shipname >> type >> s >> a >> g;
            Csillaghajo* sh;
            if      (type == "Breaker") sh = new Faltoro(shipname, s, a, g);
            else if (type == "Lander")  sh = new Partraszallo(shipname, s, a, g);
            else if (type == "Laser")   sh = new Lezerezo(shipname, s, a, g);
            sh->ved(pl);
        }
        ss->bolygok.push_back(pl);
    }

    Csillaghajo* ship;
    if (ss->maxTuzero(ship)) cout << ship->nev << endl;
    else cout << "There is no planet with starships\n";

    cout << "shield of Earth: " << ss->bolygok.front()->osszPajzs() << endl;

    cout << ss->vedtelen()->nev << " is defensless\n";

    return 0;
}*/
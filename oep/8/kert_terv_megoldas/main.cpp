#include <iostream>
#include "kertesz.h"
#include "novenyfajta.h"

using namespace std;


int main()
{
    Kert* kert = new Kert(5);
    Kertesz* jani = new Kertesz(kert);

    int jelenHonap = 3;

    jani->kert->ultet(0, Hagyma::instance(), jelenHonap);
    jani->kert->ultet(1, Burgonya::instance(), jelenHonap);
    jani->kert->ultet(2, Borso::instance(), jelenHonap);
    jani->kert->ultet(3, Tulipan::instance(), jelenHonap);
    jani->kert->ultet(4, Szegfu::instance(), jelenHonap);

    jelenHonap = 10;

    cout << "Jelenleg arathato:";
    for ( int i = 0; i < jani->kert->arathato(jelenHonap).size(); ++i){
        cout << " " << jani->kert->arathato(jelenHonap)[i];
    }
    cout << endl;

    Hagyma::destroy();
    Burgonya::destroy();
    Borso::destroy();
    Tulipan::destroy();
    Szegfu::destroy();

    delete kert;
    delete jani;
    
    return 0;
}
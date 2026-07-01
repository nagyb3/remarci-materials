#include <iostream>

#include "enor.h"

using namespace std;

int main()
{
    try{
        Enor t("inp.txt");

        for( t.first(); !t.end(); t.next() ){
            cout << t.current() << endl;
        }
    }catch(Enor::FileErrorException ex) {
        cout << "Hibas fajlnev\n";
    }
    
    return 0;
}
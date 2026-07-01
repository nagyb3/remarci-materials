#include <iostream>
#include <fstream>

using namespace std;

struct Kaktusz{
    string nev;
    string oshaza;
    string szin;
    int meret;
};

int main()
{
    ifstream x;
    x.open("inp.txt");

    ofstream y("out1.txt");
    ofstream z("out2.txt");
    
    Kaktusz e;
    while (x >> e.nev >> e.oshaza >> e.szin >> e.meret){
        if (e.szin == "piros"){
            y << e.nev << endl;
        }
        if (e.oshaza == "mexico"){
            z << e.nev << endl;
        }
    }
    x.close();
    y.close();
    z.close();
    return 0;
}
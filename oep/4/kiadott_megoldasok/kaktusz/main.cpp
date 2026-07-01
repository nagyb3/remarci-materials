#include <iostream>
#include <fstream>

using namespace std;

int main()
{
    ifstream x("inp.txt");
    if( x.fail() ){
        cerr << "Open error!\n";
        return 1;
    }

    ofstream y("out1.txt");
    if( x.fail() ){
        cerr << "Open error!\n";
        return 1;
    }

    ofstream z("out2.txt");
    if( x.fail() ){
        cerr << "Open error!\n";
        return 1;
    }

    string name, country, color;
    int height;
    while ( x >> name >> country >> color >> height ){
        if("piros"==color)    y << name << endl;
        if("mexico"==country) z << name << endl;
    }

    return 0;
}

/*
struct Cactus {
    string name, country, color;
    int height;
};

enum Status { abnorm, norm };

bool read(ifstream &f, Cactus &e, Status &st)
{
    f >> e.name >> e.country >> e.color >> e.height;
    st = f.fail() ? abnorm : norm;
    return norm==st;
}
*/

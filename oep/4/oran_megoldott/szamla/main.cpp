#include <iostream>
#include <fstream>
#include <vector>
#include <sstream>

using namespace std;

struct Elem{
    string cikk;
    int ar;

    Elem(const string& c, int a) : cikk(c), ar(a) {}
};

struct Szamla{
    string nev;
    vector<Elem> lista;
    int ossz(){
        int s = 0;
        for (int i = 0; i < lista.size(); ++i){
            s += lista[i].ar;
        }
        return s;
    }
    friend istream& operator>>(istream& is, Szamla& e);
};

istream& operator>>(istream& is, Szamla& e){
    e.lista.clear();
    string sor;
    getline(is, sor);
    istringstream ss(sor);
    ss >> e.nev;
    string tmp_cikk;
    int tmp_ar;
    while (ss >> tmp_cikk >> tmp_ar){
        e.lista.push_back(Elem(tmp_cikk, tmp_ar));
    }
    return is;
}

int main()
{
    ifstream f("input.txt");

    int sum = 0;
    Szamla sor;
    while (f >> sor){
        sum += sor.ossz();
    }
    cout << sum << endl;

    return 0;
}
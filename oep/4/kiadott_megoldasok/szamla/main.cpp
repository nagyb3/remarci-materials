#include <iostream>
#include <fstream>
#include <vector>
#include <sstream>

using namespace std;

struct Voice {
    string name;
    int totalprice;
};

ifstream& operator>>(ifstream &in, Voice &voice);
//enum Status{abnorm, norm};
//bool read(ifstream &in, Voice &voice, Status& st);

int main()
{
    ifstream f("input.txt");
    if(f.fail()) { cout << "Wrong file name!" << endl; return 1; }

    Voice voice;
//  Status st;

    int sum = 0;
    while(f >> voice){ sum += voice.totalprice; }
//  while(read(f,voice,st)){ sum += voice.totalprice; }

    cout << "Total income: " << sum << endl;

    return 0;
}

ifstream& operator>>(ifstream &f, Voice &voice)
{
    string line;
    if(getline(f, line)){
        istringstream in(line);

        string id;
        int price;

        in >> voice.name;
        voice.totalprice = 0;
        while(in >> id >> price){
            voice.totalprice += price;
        }
    }
    return f;
}
/*
bool read(ifstream &in, Voice &voice, Status& st)
{
    string line;
    if(getline(in, line)){
        st = norm;
        istringstream in(line);

        string id;
        int price;

        in >> voice.name;
        voice.totalprice = 0;
        while(in >> id >> price){
            voice.totalprice += price;
        }
    }
    else st=abnorm;
    return norm==st;
}
*/

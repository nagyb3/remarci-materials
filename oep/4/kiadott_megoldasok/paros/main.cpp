#include <iostream>
#include <fstream>

using namespace std;

int main()
{
    ifstream x("inp.txt");
    if(x.fail()){
        cerr << "File name error!\n";
        return 1;
    }
    int e;

    int dbe = 0;
    while(x >> e && e>=0){
        if(0==e%2) ++dbe;
    }
    cout << "before: " << dbe << endl;

    int dbu = 0;
    while(x >> e){
        if(0==e%2) ++dbu;
    }
    cout << "after: "  << dbu << endl;

    return 0;
}

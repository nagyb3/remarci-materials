#include <iostream>
#include <fstream>

using namespace std;

int main()
{
    ifstream x;
    x.open("inp.txt");

    bool l = true;
    
    int e;
    while (x >> e && l){
        if (e%2 != 0){
            l = false;
        }
        //l = e % 2 == 0
    }
    cout << "Mind paros-e: " << (l?"igen":"nem") << endl;
    x.close();
    return 0;
}
#include <iostream>
#include "diag.h"
#include "read.hpp"

using namespace std;

class Menu
{
public:
    Menu() { }
    void run();
private:
    Diag o[2];

    void menuWrite();
    void getElement(int x) const;
    void setElement(int x);
    void readMatrix(int x);
    void writeMatrix(int x);
    void sum();
    void mul();
};

int main()
{
    Menu m;
    m.run();
}

bool check(int n) { return 0<=n && n<=10; }

void Menu::run()
{
    int n = 0;
    do {
        menuWrite();

        n = read <int> ( "\n>>>>", "integer between 0 and 10 is needed\n", check );
        switch(n)
        {
        case 1:
            getElement(0);
            break;
        case 2:
            getElement(1);
            break;
        case 3:
            setElement(0);
            break;
        case 4:
            setElement(1);
            break;
        case 5:
            readMatrix(0);
            break;
        case 6:
            readMatrix(1);
            break;
        case 7:
            writeMatrix(0);
            break;
        case 8:
            writeMatrix(1);
            break;
        case 9:
            sum();
            break;
        case 10:
            mul();
            break;
        }
    } while(n!=0);
}

void Menu::menuWrite()
{
    cout << endl << endl;
    cout << " 0. - Quit" << endl;
    cout << " 1. - Get an element of the matrix A" << endl;
    cout << " 2. - Get an element of the matrix B" << endl;
    cout << " 3. - Overwrite an element of the matrix A" << endl;
    cout << " 4. - Overwrite an element of the matrix B" << endl;
    cout << " 5. - Read matrix A" << endl;
    cout << " 6. - Read matrix B" << endl;
    cout << " 7. - Write matrix A" << endl;
    cout << " 8. - Write matrix B" << endl;
    cout << " 9. - Add matrices" << endl;
    cout << "10. - Multiply matrices" << endl;
}

void Menu::getElement(int x) const
{
    int i,j;
    cout << "Give the index of the row: ";
    cin >> i;
    cout << "Give the index of the column: ";
    cin >> j;
    try
    {
        cout << "a[" << i << "," << j << "]= " << o[x](i-1,j-1) << endl;
    }
    catch(Diag::OverIndexedException ex) { cout << "Wrong index!" << endl; }
}

void Menu::setElement(int x)
{
    int i,j,e;
    cout << "Give the index of the row: ";
    cin >> i;
    cout << "Give the index of the column: ";
    cin >> j;
    cout << "Give the value: ";
    cin >> e;
    try
    {
        o[x](i-1,j-1) = e;
    }
    catch(Diag::OverIndexedException ex) { cout << "Wrong index!" << endl; }
    catch(Diag::ReferenceToNullPartException ex) { cout << "These indexes do not point to the diagonal!" << endl; }
}

void Menu::readMatrix(int x)
{
    try
    {
        cout << "Give the size and than the items of the matrix separated by wild spaces: ";
        cin >> o[x];
    }
    catch(Diag::WrongSizeException ex) { cout << "Wrong size!" << endl; }
}

void Menu::writeMatrix(int x)
{
    cout << o[x] << endl;
}

void Menu::sum()
{
    try
    {
        cout << "Sum of the matrices: " << endl;
        cout << o[0] + o[1] << endl;
    }
    catch(Diag::DifferentSizeException ex) { cout << "Different sizes!" << endl; }
}

void Menu::mul()
{
    try
    {
        cout << "Product of the matrices: " << endl;
        cout << o[0] * o[1] << endl;
    }
    catch(Diag::DifferentSizeException ex) { cout << "Different sizes!" << endl; }
}
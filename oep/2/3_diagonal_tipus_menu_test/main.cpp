#include <iostream>
#include "diag.h"
#include "read.hpp"

using namespace std;

//#define NORMAL_MODE
#ifdef NORMAL_MODE

//class of menu for diagonal matrix
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

#else
#define CATCH_CONFIG_MAIN
#include "catch.hpp"

TEST_CASE("create", "inp.txt")
{
    const string fileName = "inp.txt";

    ifstream in(fileName.c_str());
    if(in.fail())
    {
        cout << "File name error!" << endl;
        exit(1);
    }

    Diag c;
    in >> c; // 3
    CHECK(c(0,0) == 3);
    CHECK(c(1,1) == 2);
    CHECK(c(2,2) == 1);

    Diag b;
    in >> b; // 2
    CHECK(b(0,0) == 2);
    CHECK(b(1,1) == 1);

    Diag a;
    in >> a; // 1
    CHECK(a(0,0) == 1);
}

TEST_CASE("getting and changing an element of the matrix", "")
{
    ///Diag a( {1,1,1} );
    Diag a( {1,1,1} );
    CHECK(a(0,0) == 1);
    a(0,0) = 0;
    CHECK(a(0,0) == 0);
}

TEST_CASE("copy constructor", "inp.txt")
{
    const string fileName = "inp.txt";

    ifstream in(fileName.c_str());
    if(in.fail())
    {
        cout << "File name error!" << endl;
        exit(1);
    }

    Diag a;
    in >> a; // 3

    Diag b = a;

    CHECK(a(0,0) == b(0,0));
    CHECK(a(1,1) == b(1,1));
    CHECK(a(2,2) == b(2,2));
}

TEST_CASE("assignment operator", "inp.txt")
{
    const string fileName = "inp.txt";

    ifstream in(fileName.c_str());
    if(in.fail())
    {
        cout << "File name error!" << endl;
        exit(1);
    }

    Diag a, b; // 3
    in >> a;

    b = a; // check every non-zero item
    CHECK(a(0,0) == b(0,0));
    CHECK(a(1,1) == b(1,1));
    CHECK(a(2,2) == b(2,2));

    Diag c; // 3
    c = b = a; // check every non-zero item
    CHECK(a(0,0) == c(0,0));
    CHECK(a(1,1) == c(1,1));
    CHECK(a(2,2) == c(2,2));

    a = a; // check every non-zero item
    CHECK(a(0,0) == 3);
    CHECK(a(1,1) == 2);
    CHECK(a(2,2) == 1);
}

TEST_CASE("add", "inp2.txt")
{
    const string fileName = "inp2.txt";

    ifstream in(fileName.c_str());
    if(in.fail())
    {
        cout << "File name error!" << endl;
        exit(1);
    }

    Diag a, b, c, d, f, e, z; // 3
    in >> a >> b >> z >> e;

    c = a + b; // check every non-zero item
    CHECK(c(0,0) == 4);
    CHECK(c(1,1) == 5);
    CHECK(c(2,2) == 6);

    d = b + a; // check every non-zero item
    CHECK(c(0,0) == d(0,0));
    CHECK(c(1,1) == d(1,1));
    CHECK(c(2,2) == d(2,2));

    d = (a + b) + c;
    f = a + (b + c); // check every non-zero item
    CHECK(d(0,0) == f(0,0));
    CHECK(d(1,1) == f(1,1));
    CHECK(d(2,2) == f(2,2));

    c = a + z; // check every non-zero item
    CHECK(c(0,0) == a(0,0));
    CHECK(c(1,1) == a(1,1));
    CHECK(c(2,2) == a(2,2));
}

TEST_CASE("multiply", "inp2.txt")
{
    const string fileName = "inp2.txt";

    ifstream in(fileName.c_str());
    if(in.fail())
    {
        cout << "File name error!" << endl;
        exit(1);
    }

    Diag a, b, c, d, f, e, z; // 3
    in >> a >> b >> z >> e;

    c = a * b;
    CHECK(c(0,0) == 3);
    CHECK(c(1,1) == 6);
    CHECK(c(2,2) == 9);

    d = b * a;
    CHECK(c(0,0) == d(0,0));
    CHECK(c(1,1) == d(1,1));
    CHECK(c(2,2) == d(2,2));

    d = (a * b) * c;
    f = a * (b * c);
    CHECK(d(0,0) == f(0,0));
    CHECK(d(1,1) == f(1,1));
    CHECK(d(2,2) == f(2,2));

    c = a * e;
    CHECK(c(0,0)== a(0,0));
    CHECK(c(1,1)== a(1,1));
    CHECK(c(2,2)== a(2,2));
}

TEST_CASE("exceptions", "")
{
    Diag a(3);

    CHECK_THROWS(a(3,3) = 4);   //overindexed exception
    CHECK_THROWS(a(-1,4) = 4);  //overindexed exception

    Diag b(2), c(3), d(2);

    CHECK_THROWS(c = a + b);    //different size exception
    CHECK_THROWS(d = a * b);    //different size exception

    CHECK_THROWS(a(1,0) = 4);   //nullpart exception
    CHECK_THROWS(4 == a(1,0));  //nullpart exception
}

#endif
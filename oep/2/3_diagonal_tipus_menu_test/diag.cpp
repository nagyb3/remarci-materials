#include "diag.h"
#include <iostream>
#include <iomanip>

using namespace std;

Diag operator+(const Diag& a, const Diag& b)
{
    if(a._x.size()!= b._x.size()) throw Diag::DifferentSizeException();

    Diag c(a._x.size());

    for(unsigned int i=0; i<c._x.size(); ++i)  c._x[i] = a._x[i] + b._x[i];
    return c;
}

Diag operator*(const Diag& a, const Diag& b)
{
    if(a._x.size()!= b._x.size()) throw Diag::DifferentSizeException();

    Diag c(a._x.size());

    for(unsigned int i=0; i<c._x.size(); ++i) c._x[i] = a._x[i] * b._x[i];
    return c;
}

ostream& operator<<(ostream& s, const Diag& a)
{
    for(unsigned int i=0; i<a._x.size(); ++i){
        for(unsigned int j=0; j<a._x.size(); ++j)
            s << setw(5) << a(i,j);
        s << endl;
    }
    return s;
}

istream& operator>>(istream& s, Diag& a)
{
    cout << "Size of the matrix: ";
    int matrixSize;
    s >> matrixSize;
    if(matrixSize<0) throw Diag::WrongSizeException();
    a.reSize(matrixSize);
    for(int i=0; i < matrixSize; ++i) {
        cout << "[" << i << "," << i << "]=";
        s >> a(i,i);
    }
    return s;
}

int Diag::operator()(int i, int j) const
{
    if ((i>=int(_x.size()) || i<0 ) || (j>=int(_x.size()) || j<0 )) throw Diag::OverIndexedException();
    if (i!=j) return 0;
    return _x[i];
}

int& Diag::operator()(int i, int j)
{
    if ((i>=int(_x.size()) || i<0 ) || (j>=int(_x.size()) || j<0 )) throw Diag::OverIndexedException();
    if (i!=j) throw Diag::ReferenceToNullPartException();
    return _x[i];
}
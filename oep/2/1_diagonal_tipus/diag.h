#pragma once
#include <iostream>
#include <vector>

class Diag {
public:
    class OverIndexedException : public std::exception {};
    class ReferenceToNullPartException : public std::exception {};
    class DifferentSizeException : public std::exception {};
    class WrongSizeException : public std::exception {};

    Diag(){ _x.resize(1.0); }
    Diag(int n): _x(n, 0) { if(n<0) throw Diag::WrongSizeException(); }
    Diag(const std::vector<int> &v): _x(v) { }

    void reSize(int n) { if(n<0) throw Diag::WrongSizeException(); _x.resize(n, 0); }

    int operator()(int i, int j) const;
    int& operator()(int i, int j);

    friend Diag operator+ (const Diag& a, const Diag& b);
    friend Diag operator* (const Diag& a, const Diag& b);
    friend std::istream& operator>> (std::istream& s, Diag& a);
    friend std::ostream& operator<< (std::ostream& s, const Diag& a);
private:
    std::vector<int> _x;
};
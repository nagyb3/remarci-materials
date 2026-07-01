#pragma once
#include <iostream>
#include <vector>

class Diag {
public:

    class WrongIndexException          : public std::exception {};
    class WrongSizeException           : public std::exception {};
    class ReferenceToNullPartException : public std::exception {};
    class DifferentSizeException       : public std::exception {};

    Diag(int n = 1) {
        if (n <= 0){
            throw Diag::WrongSizeException();
        }
        x.resize(n);
    }
    Diag(const std::vector<int>& v) : x(v) {}

    int Get(int i, int j) const {
        if (i < 0 || i >= x.size() || j < 0 || j >= x.size()){
            throw Diag::WrongIndexException();
        }
        if (i == j){
            return x[i];
        } else {
            return 0;
        }
    }
    void Set(int i, int j, int e){
        if (i < 0 || i >= x.size() || j < 0 || j >= x.size()){
            throw Diag::WrongIndexException();
        }
        
        if (i == j){
            x[i] = e;
        } else {
            throw Diag::ReferenceToNullPartException();
        }
    }

    void reSize(int n){
        if (n <= 0){
            throw Diag::WrongSizeException();
        }
        x.resize(n);
    }

    friend Diag Add(const Diag& a, const Diag& b){
        if (a.x.size() != b.x.size()){
            throw Diag::DifferentSizeException();
        }
        Diag c(a.x.size());
        for (unsigned int i = 0; i < c.x.size(); ++i){
            c.x[i] = a.x[i] + b.x[i];
        }
        return c;
    }

    friend Diag Mul(const Diag& a, const Diag& b){
        if (a.x.size() != b.x.size()){
            throw Diag::DifferentSizeException();
        }
        Diag c(a.x.size());
        for (unsigned int i = 0; i < c.x.size(); ++i){
            c.x[i] = a.x[i] * b.x[i];
        }
        return c;
    }

    friend std::istream& operator>>(std::istream& is, Diag& b){
        int size;
        is >> size;
        b.reSize(size);
        for (unsigned int i=0; i < size; ++i) {
            std::cout << "[" << i << "," << i << "]=";
            int tmp_elem;
            is >> tmp_elem;
            b.Set(i,i,tmp_elem);
        }
        return is;
    }

    friend std::ostream& operator<<(std::ostream& os, const Diag& a)
    {
        for(unsigned int i=0; i<a.x.size(); ++i){
            for(unsigned int j=0; j<a.x.size(); ++j){
                if (i != j){
                    os << 0 << " ";
                } else {
                    os << a.Get(i,j) << " ";
                }
            }
            os << std::endl;
        }
        return os;
    }

private:
	std::vector<int> x;
};
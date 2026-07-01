#pragma once
#include <iostream>

class CactusHeightEnor{
    public:
        class FileErrorException : public std::exception { };
        CactusEnor(const std::string &fineName) {
            x.open(fineName);
            if(x.fail()) throw FileErrorException();
        }
        ~CactusEnor() { x.close(); }

        void first() { read(); }
        void next()  { read(); }
        int current() const { return cur; }
        bool end() const { return st == abnorm; }
    private:
        enum Status { abnorm, norm };

        std::ifstream x;
        int cur;
        Status st;

        void read(){
            st = (x >> cur) ? norm : abnorm;
        }
};
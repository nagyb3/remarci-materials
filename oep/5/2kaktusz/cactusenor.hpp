#pragma once
#include <iostream>

struct Cactus{
    std::string name;
    std::string homeland;
    std::string color;
    int height;
};

std::istream& operator>>(std::istream& is, Cactus& c){
    is >> c.name >> c.homeland >> c.color >> c.height;
    return is;
}

std::ostream& operator<<(std::ostream& os, const Cactus& c){
    os << c.name << " " << c.homeland << " " << c.color << " " << c.height;
    return os;
}

class CactusEnor{
    public:
        class FileErrorException : public std::exception { };
        CactusEnor(const std::string &fineName) {
            x.open(fineName);
            if(x.fail()) throw FileErrorException();
        }
        ~CactusEnor() { x.close(); }

        void first() { read(); }
        void next()  { read(); }
        Cactus current() const { return cur; }
        bool end() const { return st == abnorm; }
    private:
        enum Status { abnorm, norm };

        std::ifstream x;
        Cactus cur;
        Status st;

        void read(){
            st = (x >> cur) ? norm : abnorm;
        }
};
#pragma once

class Animal{
    protected:
        std::string name;
        int weight;
    public:
        Animal(const std::string& n, int w) : name(n), weight(w) {}
        virtual void print() const = 0;
        /*void print() const {
            std::cout << name << " " << weight << std::endl;
        }*/
};



class Zebra : public Animal {
    private:
        int neckLength;
    public:
        Zebra(const std::string& n, int w, int nl) : neckLength(nl), Animal(n,w) {}
        void print() const override {
            std::cout << name << " " << weight << " " << neckLength << std::endl;
        }
};

class Dog : public Animal {
    private:
        std::string owner;
    public:
        Dog(const std::string& n, int w, const std::string& o) : owner(o), Animal(n,w) {}
        void print() const override {
            std::cout << name << " " << weight << " " << owner << std::endl;
        }
};
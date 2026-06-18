#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int a, b, c;
    cin >> a >> b >> c;
    if(b>c){
        if(a<b) cout << "1"<<endl;
        else if(b<a) cout << "2"<<endl;
        else cout << "3"<<endl;
    }else{
        if(a-1<(c-b)+c-1) cout << "1"<<endl;
        else if(a-1>(c-b)+c-1) cout << "2"<<endl;
        else cout << "3"<<endl;
    }
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}
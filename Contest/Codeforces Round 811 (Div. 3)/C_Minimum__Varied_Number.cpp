#include <bits/stdc++.h>
using namespace std;
 void solution(){
    int s,mult = 1,num = 0;
    cin>>s;
    string str;
    for(int i=9; i>=1;i--){
        if(s>=i){
            s-= i;
            num += mult*i;
            mult*=10;
        }
    }
    cout<<num<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}
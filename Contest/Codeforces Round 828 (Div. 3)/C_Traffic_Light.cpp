#include<bits/stdc++.h>
#define ll long long
using namespace std;
 void solution(){
    int n;
    string str;
    char q;
    cin>> n >> q;
    vector<char>v(n+2);
    bool k = 1;
    for (int i = 1; i <= n; i++)
    {
        cin>>v[i];
        if(v[i]!='g')   k = 0;
    }
    bool m = 1;
    ll c = 0, g= 0, r = 0, y = 0;
    for (int i = n; i > 0; i--)
    {
        if(v[i]=='g')   m = 0;
        if(m)   continue;
        c++;
        if(v[i]==q) r= max(c,r);
        if(v[i]=='g')   c=0;
    }
    for (int i = n; i >0; i--)
    {
        c++;
        if(v[i]==q) r = max(r,c);
        if(v[i]=='g')   break;
    }
    if(k||q=='g')   r=0;
    cout<<r<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}
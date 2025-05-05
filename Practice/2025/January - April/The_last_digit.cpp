#include<bits/stdc++.h>
using namespace std;
#define int long long

#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)


int last_digit(int a, int b){
    int res = 1;
    while(b>0){
        if(b&1)
            res = (res*a)%10;
        a = (a*a)%10;
        b>>=1;
    }
    return res;
}


void solve()
{
    int a,b;
    cin>>a>>b;
    a = a%10;
    if(a==0)
        cout<<0<<endl;
    else
        cout<<last_digit(a,b)<<endl;
}

int32_t main()
{
    fastIO;
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        solve();
    }
}
#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


void solve()
{
    string str;
    cin>>str;
    string n1 = string(str.begin(),str.begin()+2), n2 = string(str.begin()+3, str.end());
    int num1 = stoi(n1), num2 = stoi(n2);
    while(num1!=num2 or num1%11!=0){
        num2++;
        if(num2==60){
            num1 = (num1+1)%24;
            num2 = 0;
        }
    }
    if(num1<11){
        cout<<0<<num1<<":"<<0<<num2<<endl;
    }else{
        cout<<num1<<":"<<num2<<endl;
    }
}

int32_t main()
{
    freopen("paint.in", "r", stdin);
    freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}
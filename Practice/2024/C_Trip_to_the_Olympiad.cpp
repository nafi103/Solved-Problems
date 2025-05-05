#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int msb(int n){
    int k = __builtin_clzll(n);
    return 1ll << (63 - k);
}


void solve()
{
    int l,r;
    cin>>l>>r;
    int a = r,b = 0, c = 0,sl = l, sr = r;
    while(msb(sl)==msb(sr)){
        int m = msb(sr);
        sl-=m;
        sr-=m;
        b+=m;
        c+=m;
    }
    int currMsb = msb(sr);
    currMsb>>=1;
    while((currMsb&l)){
        b+=currMsb;
        c+=currMsb;
        if(currMsb&a) a-=currMsb;
        currMsb>>=1;
    }
    b+=currMsb;
    c+=currMsb;
    if(currMsb&a) a-=currMsb;
    currMsb>>=1;
    int now = 1;
    while(currMsb){
        if(now) b+=currMsb;
        else c+=currMsb;
        currMsb>>=1;
    }
    if(b==c){
        if(c&1){
            if(c==l) c++;
            else c--;
        }else c++;
    }
    if(a==c) a++;
    cout<<a<<" "<<b<<" "<<c<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}
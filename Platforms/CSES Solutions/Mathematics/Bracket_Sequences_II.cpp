#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
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
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}

vector<int>fact, ifact,catalan;

int nCr(int n, int r){
    return ((fact[n]*ifact[r])%mod * ifact[n-r])%mod;
}

void calc(int n){
    n+=10;
    fact.resize(n+1);
    ifact.resize(n+1);
    catalan.resize(n/2);
    fact[0] = 1;
    for(int i = 1; i<=n; i++){
        fact[i] = (fact[i-1]*i)%mod;
    }
    ifact[n] = mminvprime(fact[n],mod);
    for(int i = n-1; i>=0; i--){
        ifact[i] = (ifact[i+1]*(i+1))%mod;
    }
    catalan[0] = 1;
    for(int i = 1; i<n/2; i++){
        catalan[i] = ((nCr(2*i, i) * ifact[i+1])%mod * fact[i])%mod;
    }
}


void solve()
{
    int n,extra = 0;
    cin>>n;
    calc(n);
    string str;
    cin>>str;
    if(n&1){
        cout<<0<<endl;
        return;
    }
    int rem = n-sz(str);
    for(auto &x: str){
        if(x=='(')
            extra++;
        else
            extra--;
        if(extra<0){
            cout<<0<<endl;
            return;
        }
    }
    if(extra>n-sz(str)){
        cout<<0<<endl;
        return;
    }
    int valid = n-sz(str)-extra;
    if(extra){
        if(valid)
            cout<<(nCr(n-sz(str),valid/2) - nCr(n-sz(str),valid/2 - 1) + mod)%mod<<endl;
        else
            cout<<1<<endl;
    }else{
        cout<<catalan[n-sz(str)]<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}
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

int fact[1001],invprime[1001];

int ncr(int n, int r){
    return ((fact[n]*invprime[r])%mod * invprime[n-r])%mod;
}


void solve()
{
    int n,k;
    cin>>n>>k;
    vector<int>v(n);
    readv(v);
    if(n==k){
        cout<<1<<endl;
        return;
    }
    sort(all(v));
    int x = v[n-k];
    int r = 0;
    for(int i = n-k; i<n; i++){
        if(v[i]==x)
            r++;
        else break;
    }
    int N = count(all(v),x);
    cout<<ncr(N,r)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    fact[0] = 1;
    for(int i =1; i<1001; i++){
        fact[i] = (fact[i-1]*i)%mod;
    }
    invprime[1000] = mminvprime(fact[1000],mod);
    for(int i = 999; i>=0; i--){
        invprime[i] = (invprime[i+1]*(i+1))%mod;
    }
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}
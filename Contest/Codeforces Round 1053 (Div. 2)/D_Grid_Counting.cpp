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
const int N = 2e5+1;
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}
int fact[N],ifact[N];

int nCr(int n, int r){
    if(r>n)
        return 0;
    return ((fact[n]*ifact[r])%mod * ifact[n-r])%mod;
}

void solve()
{
    int n,used = 0, ans = 1;
    cin>>n;
    vector<int>v(n+1,0); //max_black = n-2*(i-1)
    for(int i = 1; i<=n; i++){
        cin>>v[i];
    }
    if(accumulate(all(v),0ll)!=n){
        cout<<0<<endl;
        return;
    }
    for(int i = n; i>=1; i--){
        int r = v[i];
        int np = (n-2*(i-1)) - used;
        if(r)
            ans = (ans*nCr(np,r))%mod;
        used+=v[i];
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    fact[0] = 1;
    for(int i = 1; i<N; i++){
        fact[i] = (i*fact[i-1])%mod;
    }
    ifact[N-1] = mminvprime(fact[N-1],mod);
    for(int i = N-2; i>=0; i--){
        ifact[i] = (ifact[i+1]*(i+1))%mod;
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}
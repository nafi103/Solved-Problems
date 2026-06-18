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
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}

const int N = 1e5+2;
vector<int> ifact(N);


void solve()
{
    int a,b,k;
    cin>>a>>b>>k;
    int row = (k*(a-1))+1;
    int column = 1;
    for(int i = row; i>=row-a+1; i--){
        column = (column*(i%mod))%mod;
    }
    column = (column*ifact[a])%mod;
    column = (column*k)%mod;
    column = (column*(b-1))%mod;
    column = (column+1)%mod;
    column = (column+mod)%mod;
    cout<<(row%mod)<<" "<<column<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int fact = 1;
    for(int i = 2; i<N; i++){
        fact = (fact*i)%mod;
    }
    ifact[N-1] = mminvprime(fact,mod);
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
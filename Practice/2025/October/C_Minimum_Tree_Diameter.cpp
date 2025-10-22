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
    int n,k;
    cin>>n>>k;
    if(n<=2){
        cout<<n-1<<endl;
        return;
    }
    if(k==1){
        cout<<-1<<endl;
        return;
    }
    if(k==2){
        cout<<n-1<<endl;
        return;
    }
    if(n<=k+1){
        cout<<2<<endl;
        return;
    }
    int rem = n-(k+1), level = 2, nodes = k, one_side = k-1;
    k--;
    for(int i = 0; ; i++,level++){
        if(rem<=nodes*k){
            cout<<2*level-(rem<=one_side?1:0)<<endl;
            return;
        }
        rem-=nodes*k;
        nodes*=k;
        one_side*=k;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}
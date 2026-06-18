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
    vector<int>base_3;
    base_3.reserve(32);
    while(n>0){
        base_3.push_back(n%3);
        n/=3;
    }
    int deal = 0, cost = 0;
    for(int p = 0; p<sz(base_3); p++){
        deal += base_3[p];
    }
    if(deal>k){
        cout<<-1<<endl;
        return;
    }
    for(int p = sz(base_3)-1; p>=0; p--){
        if(p){
            int max_take = min(base_3[p], (k-deal)/2);
            base_3[p]-=max_take;
            base_3[p-1]+=3*max_take;
            deal+=2*max_take;
        }
        cost+=base_3[p]*pow(3,p+1);
        if(p)
            cost+=base_3[p]*p*pow(3,p-1);
    }
    cout<<cost<<endl;
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
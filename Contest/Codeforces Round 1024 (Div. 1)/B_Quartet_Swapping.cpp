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

int calc(vector<int> &v){
    pbds<int> d;
    int inv = 0;
    for(auto &x: v){
        inv+= sz(d) - d.order_of_key(x);
        d.insert(x);
    }
    return inv;
}

void solve()
{
    int n;
    cin>>n;
    vector<int>v(n);
    readv(v);
    vector<int>even,odd;
    for(int i = 0; i<n; i++){
        int x = v[i];
        if(i&1)
            odd.push_back(x);
        else
            even.push_back(x);
    }
    int inv1 = calc(even), inv2 = calc(odd);
    sort(rbegin(even),rend(even));
    sort(rbegin(odd),rend(odd));
    if((inv1&1) != (inv2&1)){
        if(n&1){
            swap(even[0],even[1]);
        }else{
            swap(odd[0],odd[1]);
        }
    }
    for(int i = 0; i<n; i++){
        if(i&1){
            cout<<odd.back()<<" ";
            odd.pop_back();
        }
        else{
            cout<<even.back()<<" ";
            even.pop_back();
        }
    }
    cout<<endl;
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
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
    int l,r;
    cin>>l>>r;
    int n = r+1;
    vector<int>b(n),a(n);
    iota(b.rbegin(),b.rend(),0);
    set<int>available;
    for(int i = 0; i<n; i++){
        available.insert(i);
    }
    for(int i = 0; i<n; i++){
        int &curr = b[i];
        for(int j = 20; j>=0; j--){
            int need = ((1<<j)-1)&(~curr);
            if(available.count(need)){
                a[i]=need;
                available.erase(need);
                break;
            }
        }
    }
    reverse(all(a));
    reverse(all(b));
    int sum = 0;
    for(int i = 0; i<n; i++){
        sum+=(a[i]|b[i]);
    }
    cout<<sum<<endl;
    for(auto &x: a)
        cout<<x<<" ";
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
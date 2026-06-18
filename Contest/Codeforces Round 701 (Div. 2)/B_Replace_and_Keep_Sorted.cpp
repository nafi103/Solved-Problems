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
    int n,q,k;
    cin>>n>>q>>k;
    vector<int>left(n,0),right(n,0),v(n);
    readv(v);
    left[0] = v[0]-1;
    right[n-1] = k-v[n-1];
    for(int i = 0; i<n; i++){
        if(i<n-1){
            right[i]=v[i+1]-v[i]-1;
        }
        if(i){
            left[i] = v[i]-v[i-1]-1;
        }
    }
    for(int i = 1; i<n; i++){
        left[i]+=left[i-1];
        right[i]+=right[i-1];
    }
    while(q--){
        int l,r,ans = 0;
        cin>>l>>r;
        l--;r--;
        if(l==r){
            cout<<k-1<<endl;
            continue;
        }
        ans+=left[r]-left[l];
        if(r)
            ans+=right[r-1];
        if(l)
            ans-=right[l-1];
        ans+=v[l]-1;
        ans+=k-v[r];
        cout<<ans<<endl;
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
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
int n,k,al,ar;
int v[300000], a[300000];
 bool check(int m){
    int mx = -inf;
    for(int i = 0; i<n; i++){
        if(v[i]>=m)
            a[i] = 1;
        else
            a[i] = -1;
        if(i)
            a[i]+=a[i-1];
    }
    int mn = 0, l = -1, r = k-1,cl = -1;
    for(r; r<n; r++){
        if(a[r]-mn >= 0){
            ar = r;
            al = cl+1;
            return true;
        }
        l++;
        if(a[l]<mn){
            mn = a[l];
            cl = l;
        }
    }
    return false;
}
 int bs(int l, int r){
    if(l>r)
        return r;
    int mid = (l+r)/2;
    if(check(mid))
        return bs(mid+1,r);
    return bs(l,mid-1);
}
 void solve()
{
    cin>>n>>k;
    for(int i = 0; i<n; i++)
        cin>>v[i];
    int ans = bs(0,n+1);
    cout<<ans<<" "<<++al<<" "<<++ar<<endl;
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
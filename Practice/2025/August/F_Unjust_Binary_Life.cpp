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
    int n;
    cin>>n;
    int cnta = 0, cntb = 0, sub = 0;
    vector<int>pa(n+1,-inf),pb(n+1,-inf),prefa(n+1,0),prefb(n+1,0);
    for(int i = 1; i<=n; i++){
        char c;
        cin>>c;
        cnta+=(c-'0');
        pa[i] = 2*cnta - i;
    }
    for(int i = 1; i<=n; i++){
        char c;
        cin>>c;
        cntb+=(c-'0');
        pb[i] = i - 2*cntb;
    }
    sort(all(pa));
    sort(all(pb));
    for(int i = 1; i<=n; i++){
        prefa[i] = prefa[i-1]+pa[i];
        prefb[i] = prefb[i-1]+pb[i];
    }
    for(int i = n, j = n, k = n; i>=1; i--){
        while(pa[i]<pb[j])
            j--;
        while(pb[i]<pa[k])
            k--;
        sub += (j*pa[i] - prefb[j]);
        sub += (k*pb[i] - prefa[k]);
    }
    sub/=2;
    cout<<(n*n*(n+1))/2 - sub<<endl;
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
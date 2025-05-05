#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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

int f(int x1,int y1,int z1, int x2, int y2, int z2, int k){
    vector<int>d;
    int ans = 0;
    d.pb(abs(x1-x2));
    d.pb(abs(y1-y2));
    d.pb(abs(z1-z2));
    sort(all(d));
    ans+=3*d[0];
    d[1]-=d[0];
    d[2]-=d[0];
    d.erase(d.begin());
    ans+=2*d[0];
    d[1]-=d[0];
    d.erase(d.begin());
    int remK = d[0]/k - (d[0]%k==0);
    ans+=d[0];
    ans+=remK;
    if(remK%2==1) ans++;
    return ans;
}


void solve()
{
    int x1,y1,z1,x2,y2,z2,k;
    cin>>x1>>y1>>z1>>x2>>y2>>z2>>k;
    int ans = inf;
    ans = min(ans,f(x1,y1,z1,x2,y2,z2,k));
    cout<<ans<<endl;
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
        // google(z);
        solve();
    }
}
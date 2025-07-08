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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
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


void solve()
{
    int n,ans = 0;
    cin>>n;
    vector<array<int,3>>v;
    v.reserve(2*n);
    for(int i = 0; i<n; i++){
        int x1,y1,x2,y2;
        cin>>x1>>y1>>x2>>y2;
        v.push_back({x1,y1,y2});
        v.push_back({x2,y2,y1});
    }
    sort(all(v));
    multiset<int> low,high;
    low.insert(v[0][1]);
    high.insert(v[0][2]);
    for(int i = 1; i<2*n; i++){
        int x = v[i][0]-v[i-1][0], y = *high.rbegin() - *low.begin();
        ans+=(x*y);
        if(v[i][1]<v[i][2]){
            low.insert(v[i][1]);
            high.insert(v[i][2]);
        }else{
            low.erase(low.find(v[i][2]));
            high.erase(high.find(v[i][1]));
        }
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
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}
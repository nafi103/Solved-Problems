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


void solve()
{
    int n,m;
    cin>>n>>m;
    vector<int>a,b(m);
    int kevin;
    cin>>kevin;
    a.pb(kevin);
    for(int i = 1; i<n; i++){
        int x;
        cin>>x;
        if(x>kevin) a.pb(x);
    }
    n = sz(a);
    readv(b);
    sort(all(a));
    sort(all(b));
    debug(a) debug(b);
    int kevin_can_solve = upper_bound(all(b),kevin) - b.begin() - 1;
    vector<int> pref(m,0);
    for(int i = 1; i<n; i++){
        int pos = upper_bound(all(b),a[i]) - b.begin() - 1;
        if(pos!=-1) pref[pos]++;
    }
    for(int i = m-2; i>=0; i--) pref[i]+=pref[i+1];
    for(int i = kevin_can_solve; i>=0; i--){
        pref[i] = 0;
    }
    for(int i = 0; i<m; i++) pref[i]++;
    sort(all(pref));
    for(int k = 1; k<=m; k++){
        int ans = 0;
        for(int j = k-1; j<m; j+=k){
            ans+=pref[j];
        }
        cout<<ans<<" ";
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
        // google(z);
        solve();
    }
}
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

int sq(int n){
    return n*n;
}

void solve()
{
    int n,m;
    cin>>n>>m;
    using pii = pair<int,int>;
    vector<pii>c(n);
    for(auto &[x,r]: c)
        cin>>x;
    for(auto &[x,r]: c)
        cin>>r;
    sort(all(c),[&](pii &a, pii &b){
        if(a.ff-a.ss!=b.ff-b.ss)
            return a.ff-a.ss<b.ff-b.ss;
        return a.ss>b.ss;
    });
    vector<pii>tmp;
    pii prev = {-inf,INT_MAX};
    for(int i = 0; i<n; i++){
        if(c[i].ff-c[i].ss>=prev.ff - prev.ss and c[i].ff+c[i].ss<=prev.ff+prev.ss)
            continue;
        prev = c[i];
        tmp.push_back(c[i]);
    }
    c = tmp;
    n = sz(c);
    int i = 0, j = 0,ans = 0;
    int p = c[0].ff-c[0].ss;
    while(i<n){
        j = max(i,j);
        while(j+1<n and c[j+1].ff-c[j+1].ss<=p)
        j++;
        int mx = 0;
        for(int k = i; k<=j; k++){
            mx = max(mx, (int)sqrt(sq(c[k].ss) - sq(c[k].ff-p)));
        }
        ans+=2*mx+1;
        p++;
        while(i<n and c[i].ff+c[i].ss<p)
            i++;
        if(i<n and c[i].ff - c[i].ss>p){
            p = c[i].ff-c[i].ss;
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
        // google(z);
        solve();
    }
}
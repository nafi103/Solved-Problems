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
int n,k;
vector<int>v;

bool check(int mx){
    int walk = 0,cnt = 1;
    for(int i = 0; i<n; i++){
        if(walk+v[i]<=mx){
            walk+=v[i];
        }else{
            cnt++;
            walk = v[i];
        }
    }
    return walk<=mx and cnt<=k;
}

int bs(int l, int r){
    if(l>r)
        return l;
    int mid = (l+r)/2;
    if(check(mid))
        return bs(l,mid-1);
    return bs(mid+1,r);
}

void solve()
{
    v.clear();
    cin>>n>>k;
    n++,k++;
    v.resize(n);
    readv(v);
    int ans = bs(*max_element(all(v)),1e10),walk = 0;
    vector<int>go;
    for(int i = 0; i<n; i++){
        if(walk+v[i]<=ans and n-i>=k-sz(go)){
            walk+=v[i];
        }else{
            go.push_back(walk);
            walk = v[i];
        }
    }
    go.push_back(walk);
    cout<<ans<<endl;
    for(auto &x: go)
        cout<<x<<endl;
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
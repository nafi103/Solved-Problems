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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int n,k;

int bs(vector<pair<int,int>>&v, int &need, int l, int r){
    if(l>r) return l;
    int mid = (l+r)/2;
    if(v[mid].ff<need) return bs(v,need,mid+1,r);
    return bs(v,need,l,mid-1);
}


void solve()
{
    cin>>n>>k;
    vector<pair<int,int>>v(n);
    for(int i= 0; i<n; i++){
        cin>>v[i].ff;
        v[i].ss = i+1;
    }
    sort(all(v));
    for(int i = 0; i<n-1; i++){
        for(int j = i+1; j<n; j++){
            int need = k-v[i].ff-v[j].ff;
            if(need<=0) break;
            int pos = bs(v,need,0,n-1);
            while(pos<n and (pos==i or pos==j)) pos++;
            if(pos<n and v[pos].ff==need){
                cout<<v[i].ss<<" "<<v[j].ss<<" "<<v[pos].ss<<endl;
                return;
            }
        }
    }
    cout<<"IMPOSSIBLE"<<endl;
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
        // google(z);
        solve();
    }
}
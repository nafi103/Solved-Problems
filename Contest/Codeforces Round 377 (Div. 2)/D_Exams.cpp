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

vector<int>distinct,v, prep;
int n,m;

bool check(int day){
    if(distinct[day]<m) return false;
    vector<bool>visited(m+1,false);
    vector<pair<int,int>>exam;
    for(int i = day; i>=1; i--){
        if(v[i] and !visited[v[i]]){
            exam.pb({i,v[i]});
            visited[v[i]] = true;
        }
    }
    sort(all(exam));
    int used = 0;
    for(auto &[d,e]: exam){
        if(d-1-used<prep[e]){
            return false;
        }else{
            used+=(prep[e]+1);
        }
    }
    return true;
}

int bs(int l, int r){
    if(l>r) return l;
    int mid = (l+r)/2;
    if(check(mid)) return bs(l,mid-1);
    else return bs(mid+1,r);
}


void solve()
{
    cin>>n>>m;
    distinct.assign(n+1,0); v.resize(n+1); prep.resize(m+1);
    vector<bool>visited(m+1,false);
    for(int i = 1; i<=n; i++) cin>>v[i];
    for(int i = 1; i<=m; i++) cin>>prep[i];
    for(int i = 1; i<=n; i++){
        distinct[i] = distinct[i-1];
        if(v[i] and !visited[v[i]]){
            distinct[i]++;
            visited[v[i]] = true;
        }
    }
    int ans = bs(1,n);
    cout<<(ans>n? -1: ans)<<endl;
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
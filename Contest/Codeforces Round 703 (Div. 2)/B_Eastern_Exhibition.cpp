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
#define x first
#define y second
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
using pii = pair<int,int>;

int distance(pii &a, pii &b){
    return abs(a.x-b.x)+abs(a.y-b.y);
}


void solve()
{
    int n;
    cin>>n;
    vector<pii>point(n);
    for(int i = 0; i<n; i++){
        cin>>point[i].x>>point[i].y;
    }
    if(n&1){
        cout<<1<<endl;
    }else{
        int mid2 = n/2,mid1 = mid2-1;
        sort(all(point),[&](pii &a, pii &b){
            return a.x<b.x;
        });
        int dx = point[mid2].x - point[mid1].x + 1;
        sort(all(point),[&](pii &a, pii &b){
            return a.y<b.y;
        });
        int dy = point[mid2].y - point[mid1].y + 1;
        cout<<dx*dy<<endl;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}
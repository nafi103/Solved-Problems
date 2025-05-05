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

string str,rev_str;
int n,start = 0;
vector<set<int>>for_str,for_rev_str;

bool go(int len, int type){
    string tstr = (type?rev_str:str);
    vector<set<int>> tmp = (type?for_rev_str:for_str);
    int r = min(n-1,start+len-1);
    for(int i = start; i<n; i++){
        if(tstr[i]!=tstr[n-1-i]){
            if(i>r) return false;
            int alp = tstr[n-1-i] - 'a',now = tstr[i]-'a';
            auto next_pos_i = tmp[alp].upper_bound(i);
            if(next_pos_i==tmp[alp].end() or *next_pos_i>r){
                return false;
            }else{
                int pos = *next_pos_i;
                tmp[alp].erase(pos);
                tmp[now].erase(i);
                tmp[now].insert(pos);
                swap(tstr[pos],tstr[i]);
            }
        }
    }
    return true;
}

bool check(int len){
    bool flag =  go(len,0);
    if(!flag) flag|=go(len,1);
    return flag;
}

int bs(int l, int r){
    if(l>r) return l;
    int mid = (l+r)/2;
    if(check(mid)) return bs(l,mid-1);
    else return bs(mid+1,r);
}


void solve()
{
    cin>>str;
    n = sz(str);
    for_str.resize(26);
    for_rev_str.resize(26);
    bool flag = true;
    for(int i = 0; i<n ;i++){
        if(str[i]!=str[n-i-1]){
            flag = false;
            break;
        }
    }
    if(flag){
        cout<<0<<endl;
        return;
    }
    rev_str = str;
    reverse(all(rev_str));
    start = 0;
    while(str[start]==str[n-start-1]) start++;
    for(int i = 0; i<n; i++){
        if(i<start or i>n-1-start) continue;
        int x = str[i]-'a';
        int y = rev_str[i] - 'a';
        for_str[x].insert(i);
        for_rev_str[y].insert(i);
    }
    cout<<bs(1,n)<<endl;
    for_str.clear();
    for_rev_str.clear();
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
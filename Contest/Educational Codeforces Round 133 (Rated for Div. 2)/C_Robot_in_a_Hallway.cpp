#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 struct Node
{
    int value;
     Node(int val = -inf) : value(val) {} // min -> inf, sum -> 0, max -> -inf
};
 Node merge(Node &left, Node &right)
{
    return Node(max(left.value, right.value));
}
 struct Segment_Tree
{
    int n;
    vector<int> v;
    vector<Node> st;
     Segment_Tree(vector<int> &_v, int _n)
    {
        n = _n;
        st.resize(4 * n);
        v = _v;
        build(1, 1, n);
    }
     void build(int node, int b, int e)
    {
        if (b == e)
        {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        st[node] = merge(st[left], st[right]);
    }
     Node query(int node, int b, int e, int &l, int &r)
    {
        if (e < l or b > r)
            return Node();
        if (b >= l and e <= r)
        {
            return st[node];
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r), query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }
     int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }
};
 int dp[200005][2];
int reach[200005][2];
vector<int> up, down, rev_up, rev_down;
vector<int> time_up, time_down, time_rup, time_rdown; //normal move
 int bs(int b, int e, int target, Segment_Tree &st){
    int l = b, r = e;
    while(l <= r){
        int mid = (l + r) / 2;
        int mx = st.query(b, mid);
        if(mx > target)
            r = mid - 1;
        else
            l = mid + 1;
    }
    return l;
}
 int f(int i, int j, int &n, Segment_Tree &st_up, Segment_Tree &st_down, 
      Segment_Tree &st_rup, Segment_Tree &st_rdown){
        if(i == n){
        return dp[i][j] = reach[i][j ^ 1];
    }
        int &ans = dp[i][j];
    if(ans != -1) return ans;
        ans = f(i + 1, j ^ 1, n, st_up, st_down, st_rup, st_rdown);
    int must_time = reach[i][j];
    int r_id = n - i + 1;
     if(j & 1){
        int down_end;
        if (i + 1 > n) {
            down_end = must_time;
        } else {
            int max_val = st_down.query(i + 1, n);
            down_end = max(must_time + (n - i), max_val + n + 1);
        }
         int new_time = max(up[n] + 1, down_end + 1);
        int rev_up_end;
                if (2 > r_id) {
            rev_up_end = new_time;
        } else {
            int max_val_rev = st_rup.query(2, r_id);
            rev_up_end = max(new_time + r_id - 1, max_val_rev + r_id + 1);
        }
        return ans = min(ans, rev_up_end);
            } else {
        int up_end;
        if (i + 1 > n) {
            up_end = must_time;
        } else {
            int max_val = st_up.query(i + 1, n);
            up_end = max(must_time + (n - i), max_val + n + 1);
        }
         int new_time = max(down[n] + 1, up_end + 1);
        int rev_down_end;
                if (2 > r_id) {
            rev_down_end = new_time;
        } else {
            int max_val_rev = st_rdown.query(2, r_id);
            rev_down_end = max(new_time + r_id - 1, max_val_rev + r_id + 1);
        }
        return ans = min(ans, rev_down_end);
    }
}
 void input(){
    up.clear();
    down.clear();
    int n;
    cin >> n;
    for(int i = 1; i <= n; i++){
        for(int j = 0; j < 2; j++)
            dp[i][j] = -1;
    }
    up.resize(n + 1);
    down.resize(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> up[i];
    }
    for(int i = 1; i <= n; i++){
        cin >> down[i];
    }
    reach[1][0] = 0;
    reach[1][1] = max(1ll, down[1] + 1);
    for(int i = 2; i <= n; i++){
        if(i & 1){
            reach[i][0] = max(reach[i - 1][0] + 1, up[i] + 1);
            reach[i][1] = max(down[i] + 1, reach[i][0] + 1);
        }else{
            reach[i][1] = max(down[i] + 1, reach[i - 1][1] + 1);
            reach[i][0] = max(up[i] + 1, reach[i][1] + 1);
        }
    }
    rev_up = up;
    rev_down = down;
    reverse(rev_up.begin() + 1, rev_up.end());
    reverse(rev_down.begin() + 1, rev_down.end());
    time_up.assign(n + 1, -1);
    time_down.assign(n + 1, -1);
    time_rup.assign(n + 1, -1);
    time_rdown.assign(n + 1, -1);
    for(int i = 1; i <= n; i++){
        time_up[i] = max(time_up[i - 1] + 1, up[i] + (i > 1));
        time_down[i] = max(time_down[i - 1] + 1, down[i] + 1);
    }
    time_rup[1] = max(time_down[n] + 1, rev_up[1] + 1);
    time_rdown[1] = max(time_up[n] + 1, rev_down[1] + 1);
    for(int i = 2; i <= n; i++){
        time_rup[i] = max(rev_up[i] + 1, time_rup[i - 1] + 1);
        time_rdown[i] = max(rev_down[i] + 1, time_rdown[i - 1] + 1);
    }
}
 void solve()
{
    input();
    debug(time_up) debug(time_down) debug(time_rup) debug(time_rdown)
    int n = sz(up) - 1;
    for(int i = 1; i <= n; i++){
        up[i] -= i;
        down[i] -= i;
        rev_up[i] -= i;
        rev_down[i] -= i;
    }
    Segment_Tree st_up(up, n), st_down(down, n), st_rup(rev_up, n), st_rdown(rev_down, n);
    for(int i = 1; i <= n; i++){
        up[i] += i;
        down[i] += i;
        rev_up[i] += i;
        rev_down[i] += i;
    }
    cout << f(1, 0, n, st_up, st_down, st_rup, st_rdown) << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}
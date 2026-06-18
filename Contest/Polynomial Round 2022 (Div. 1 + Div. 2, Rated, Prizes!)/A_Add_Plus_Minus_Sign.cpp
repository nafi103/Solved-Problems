#include<bits/stdc++.h>
using namespace std;
 void solution(){
    int n,value=0;
    string str;
    cin>>n>>str;
    if(str[0]=='1') value++;
    for(int i=1;i<n;i++){
        if(str[i]=='0') cout<<"+";
        else if(str[i]=='1'&&value==0){
            cout<<"+";
            value++;
        }else{
            value--;
            cout<<"-";
        }
    }
    cout<<endl;
}
 int main(){
    int t;
    cin>>t;
    while (t--) solution();
}